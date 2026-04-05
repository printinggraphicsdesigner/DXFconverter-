"""
Flaremo DXF Converter - Flask Web API
Lectra Modaris Compatible - Clean Output with All Marks
"""
VERSION = "v6.0"
from flask import Flask, request, jsonify, send_file
from flask_cors import CORS
import os, io, base64, math, re, tempfile, shutil, atexit
from reportlab.pdfgen import canvas as pdf_canvas
from reportlab.lib.units import cm
import ezdxf
from ezdxf import recover as dxf_recover
from PIL import Image, ImageDraw

app = Flask(__name__)
CORS(app)
app.config['MAX_CONTENT_LENGTH'] = 50 * 1024 * 1024

UPLOAD_FOLDER = tempfile.mkdtemp()
OUTPUT_FOLDER = tempfile.mkdtemp()
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['OUTPUT_FOLDER'] = OUTPUT_FOLDER

# Colors (Desktop App exact)
LAYER_COLORS = {"1": (255,255,255), "14": (100,220,100), "8": (255,200,60), "4": (255,120,120), "7": (50,50,80)}
DEFAULT_COLOR = (79, 142, 247)
GRADE_COLORS = [(255,80,80), (255,165,40), (230,230,50), (255,255,255), (80,210,80), (60,160,255), (200,80,255)]
GRADE_COLORS_HEX = ["#FF5050", "#FFA528", "#E6E632", "#FFFFFF", "#50D250", "#3CA0FF", "#C850FF"]

active_parser = {}

class RULParser:
    def __init__(self):
        self.sizes, self.sample, self.sample_idx, self.rules = [], "M", 3, {}
    
    def parse(self, filepath):
        with open(filepath, "rb") as f:
            text = f.read().decode("latin-1", errors="replace")
        m = re.search(r"SIZE LIST:\s*(.+)", text)
        if m: self.sizes = m.group(1).strip().split()
        m = re.search(r"SAMPLE SIZE:\s*(\S+)", text)
        if m:
            self.sample = m.group(1).strip()
            if self.sample in self.sizes: self.sample_idx = self.sizes.index(self.sample)
        blocks = re.split(r"RULE:\s*DELTA\s+(\d+)", text)
        for i in range(1, len(blocks)-1, 2):
            pairs = re.findall(r"(-?\d+\.?\d*),\s*(-?\d+\.?\d*)", blocks[i+1])
            if pairs: self.rules[int(blocks[i])] = [(float(x), float(y)) for x,y in pairs]
    
    def get_delta_mm(self, rule_num, size_idx):
        return self.rules[rule_num][size_idx] if rule_num in self.rules and size_idx < len(self.rules[rule_num]) else (0.0, 0.0)

def _arc_length(pts, i1, i2):
    return sum(math.hypot(pts[k+1][0]-pts[k][0], pts[k+1][1]-pts[k][1]) for k in range(i1, i2))

def compute_graded_poly(base_pts, grade_indices, rul, size_idx):
    n = len(base_pts) - 1
    if not grade_indices: return list(base_pts)
    deltas = {gi: tuple(v*0.1 for v in rul.get_delta_mm(r, size_idx)) for gi, r in grade_indices}
    graded = []
    for pi, pt in enumerate(base_pts):
        pim = pi % n
        if pim in deltas:
            graded.append((pt[0]+deltas[pim][0], pt[1]+deltas[pim][1]))
            continue
        prev = next((g for g in grade_indices if g[0] <= pim), grade_indices[-1])
        nxt = next((g for g in grade_indices if g[0] >= pim), grade_indices[0])
        da, db = deltas[prev[0]], deltas[nxt[0]]
        t = _arc_length(base_pts, prev[0], pim) / _arc_length(base_pts, prev[0], nxt[0]) if prev[0] != nxt[0] else 0
        t = max(0, min(1, t))
        graded.append((pt[0] + da[0] + t*(db[0]-da[0]), pt[1] + da[1] + t*(db[1]-da[1])))
    return graded

class AAMAParser:
    def __init__(self):
        self.entities, self.bounds, self.scale = [], None, 0.1
        self.metadata, self.grade_indices, self.rul_parser = {}, [], None
        self.graded_polys, self._base_cut_polys = {}, []
    
    def parse(self, filepath):
        self.entities, self.metadata, self.grade_indices = [], {}, []
        self.graded_polys, self._base_cut_polys = {}, []
        doc, _ = dxf_recover.readfile(filepath)
        msp = doc.modelspace()
        
        # Parse blocks (Desktop App exact logic)
        for ent in msp:
            if ent.dxftype() == "INSERT":
                block = doc.blocks.get(ent.dxf.name)
                if block: self._parse_block(block)
        
        if not self.entities: self._parse_entities(msp)
        self._update_bounds()
    
    def _parse_block(self, block):
        # Scale detection (Desktop App exact)
        raw = [v.dxf.location.x for e in block if e.dxftype()=="POLYLINE" for v in e.vertices]
        if not raw: return
        sc = 0.1 if max(raw)-min(raw) > 200 else 1.0
        self.scale = sc
        
        # Collect grade points (#1, #2, etc.)
        rules = {}
        for e in block:
            if e.dxftype()=="TEXT" and re.match(r"^#\s*\d+$", e.dxf.text.strip()) and str(e.dxf.layer)=="1":
                p = e.dxf.insert
                rules[(round(p.x*sc,3), round(p.y*sc,3))] = int(re.search(r"\d+", e.dxf.text).group())
        
        # Parse ALL geometry (Desktop App exact - includes ALL entities)
        for e in block:
            t, lay = e.dxftype(), str(getattr(e.dxf, "layer", "1"))
            
            if t == "POLYLINE":
                pts = [(v.dxf.location.x*sc, v.dxf.location.y*sc) for v in e.vertices]
                if e.is_closed and pts and pts[0]!=pts[-1]: pts.append(pts[0])
                if pts:
                    self._add("POLYLINE", pts, lay)
                    if lay=="1":
                        self._base_cut_polys.append(pts)
                        gi = [(i, rules[(round(p[0],3), round(p[1],3))]) for i,p in enumerate(pts[:-1]) if (round(p[0],3), round(p[1],3)) in rules]
                        if gi and not self.grade_indices: self.grade_indices = gi
            
            elif t == "LWPOLYLINE":
                pts = [(p[0]*sc, p[1]*sc) for p in e.get_points()]
                if e.closed and pts and pts[0]!=pts[-1]: pts.append(pts[0])
                if pts: self._add("LWPOLYLINE", pts, lay)
            
            elif t == "SPLINE":
                # FIXED: tolerance 0.1 (Desktop App uses 0.5, but CLO uses 0.01-0.1)
                try:
                    pts = [(p[0]*sc, p[1]*sc) for p in e.flattening(0.1)]
                    if pts: self._add("SPLINE", pts, lay)
                except: pass
            
            elif t == "LINE":
                s, e2 = e.dxf.start, e.dxf.end
                self._add("LINE", [(s.x*sc, s.y*sc), (e2.x*sc, e2.y*sc)], lay)
            
            elif t == "ARC":
                # Dynamic steps (Desktop App: 64, but we use dynamic for smooth curves)
                cx, cy = e.dxf.center.x*sc, e.dxf.center.y*sc
                r = e.dxf.radius*sc
                sa, ea = math.radians(e.dxf.start_angle), math.radians(e.dxf.end_angle)
                if ea < sa: ea += 2*math.pi
                steps = max(128, int(r*(ea-sa)*10*2))
                pts = [(cx+r*math.cos(sa+(ea-sa)*i/steps), cy+r*math.sin(sa+(ea-sa)*i/steps)) for i in range(steps+1)]
                if pts: self._add("ARC", pts, lay)
            
            elif t == "CIRCLE":
                cx, cy, r = e.dxf.center.x*sc, e.dxf.center.y*sc, e.dxf.radius*sc
                steps = max(256, int(2*math.pi*r*10*2))
                pts = [(cx+r*math.cos(2*math.pi*i/steps), cy+r*math.sin(2*math.pi*i/steps)) for i in range(steps+1)]
                self._add("CIRCLE", pts, lay)
            
            elif t in ("TEXT", "MTEXT"):
                # Parse ALL text (size labels, annotations, etc.)
                try:
                    pos = e.dxf.insert
                    txt = e.dxf.text if t=="TEXT" else e.plain_mtext()
                    txt = txt.strip()
                    px, py = pos.x*sc, pos.y*sc
                    if txt and not re.match(r"^#\s*\d+$", txt):
                        h = max(getattr(e.dxf, "height", 3)*sc, 0.2)
                        self._add("TEXT", [(px, py)], lay, text=txt, height=h)
                except: pass
    
    def _parse_entities(self, container):
        raw = [p[0] for e in container if e.dxftype()=="LWPOLYLINE" for p in e.get_points()]
        sc = 0.1 if raw and max(raw)>200 else 1.0
        self.scale = sc
        for e in container:
            t, lay = e.dxftype(), str(getattr(e.dxf, "layer", "1"))
            if t == "LINE":
                s, e2 = e.dxf.start, e.dxf.end
                self._add("LINE", [(s.x*sc, s.y*sc), (e2.x*sc, e2.y*sc)], lay)
            elif t == "LWPOLYLINE":
                pts = [(p[0]*sc, p[1]*sc) for p in e.get_points()]
                if pts: self._add("LWPOLYLINE", pts, lay)
            elif t == "SPLINE":
                try:
                    pts = [(p[0]*sc, p[1]*sc) for p in e.flattening(0.1)]
                    if pts: self._add("SPLINE", pts, lay)
                except: pass
            elif t in ("TEXT", "MTEXT"):
                try:
                    pos = e.dxf.insert
                    txt = e.dxf.text if t=="TEXT" else e.plain_mtext()
                    txt = txt.strip()
                    px, py = pos.x*sc, pos.y*sc
                    if txt:
                        h = max(getattr(e.dxf, "height", 3)*sc, 0.2)
                        self._add("TEXT", [(px, py)], lay, text=txt, height=h)
                except: pass
    
    def attach_rul(self, rul):
        self.rul_parser = rul
        self.graded_polys = {}
        if not self._base_cut_polys or not rul.sizes: return
        for si, sn in enumerate(rul.sizes):
            self.graded_polys[sn] = [compute_graded_poly(bp, self.grade_indices, rul, si) for bp in self._base_cut_polys]
        self._update_bounds(include_graded=True)
    
    def _update_bounds(self, include_graded=False):
        xs, ys = [], []
        for e in self.entities:
            for p in e["points"]: xs.append(p[0]); ys.append(p[1])
        if include_graded:
            for polys in self.graded_polys.values():
                for poly in polys:
                    for p in poly: xs.append(p[0]); ys.append(p[1])
        if xs: self.bounds = (min(xs), min(ys), max(xs), max(ys))
    
    def _add(self, etype, pts, layer, text=None, height=None):
        ent = {"type": etype, "points": pts, "layer": layer, "color": LAYER_COLORS.get(layer, DEFAULT_COLOR)}
        if text: ent["text"] = text
        if height: ent["height"] = height
        self.entities.append(ent)

class PreviewRenderer:
    BG = (13, 13, 18)
    
    def render(self, parser, cw, ch, zoom=1.0):
        img = Image.new("RGB", (cw, ch), self.BG)
        draw = ImageDraw.Draw(img)
        if not parser.entities or not parser.bounds: return img
        
        b = parser.bounds
        dw, dh = (b[2]-b[0]) or 1, (b[3]-b[1]) or 1
        margin = 60
        base = min((cw-2*margin)/dw, (ch-2*margin)/dh) * 0.90 * zoom
        cx, cy = cw/2, ch/2
        mxc, myc = (b[0]+b[2])/2, (b[1]+b[3])/2
        tx = lambda x: cx + (x-mxc)*base
        ty = lambda y: cy - (y-myc)*base
        
        # Draw graded sizes (Desktop App exact - thin colored lines)
        if parser.graded_polys and parser.rul_parser:
            for si, sn in enumerate(parser.rul_parser.sizes):
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                width = 2 if sn == parser.rul_parser.sample else 1
                for poly in parser.graded_polys.get(sn, []):
                    if len(poly) < 2: continue
                    sc2 = [(int(tx(p[0])), int(ty(p[1]))) for p in poly]
                    for i in range(len(sc2)-1):
                        if all(0 <= c <= cw if i==0 else 0 <= c <= ch for c in [sc2[i][0], sc2[i][1], sc2[i+1][0], sc2[i+1][1]]):
                            draw.line([sc2[i], sc2[i+1]], fill=col, width=width)
                    
                    # SIZE LABEL (Desktop App exact - bottom-left of each poly)
                    gxs = [p[0] for p in poly]
                    gys = [p[1] for p in poly]
                    lx, ly = min(gxs), min(gys) - 0.7
                    label_x, label_y = int(tx(lx)), int(ty(ly))
                    if 0 <= label_x <= cw-60 and 0 <= label_y <= ch-15:
                        # Draw text background
                        draw.rectangle([label_x-2, label_y-12, label_x+55, label_y+2], fill=(0,0,0))
                        draw.text((label_x, label_y-10), f"Size: {sn}", fill=col, font_size=10)
        
        # Draw ALL entities (Desktop App exact - cut, sew, grain, notches, text)
        order = ["7", "2", "13", "14", "8", "4", "1"]
        by_lay = {}
        for e in parser.entities: by_lay.setdefault(e.get("layer", "1"), []).append(e)
        draw_order = []
        for l in order: draw_order.extend(by_lay.get(l, []))
        for l, es in by_lay.items():
            if l not in order: draw_order.extend(es)
        
        for ent in draw_order:
            pts, lay = ent["points"], ent.get("layer", "1")
            col = ent.get("color", DEFAULT_COLOR)
            
            if ent["type"] == "TEXT":
                if pts:
                    sx, sy = int(tx(pts[0][0])), int(ty(pts[0][1]))
                    if 0 <= sx <= cw-40 and 0 <= sy <= ch-15:
                        draw.text((sx, sy), ent.get("text", " ")[:40], fill=col)
                continue
            
            if len(pts) < 2: continue
            width = 2 if lay == "1" else 1
            sc2 = [(int(tx(p[0])), int(ty(p[1]))) for p in pts]
            for i in range(len(sc2)-1):
                if all(0 <= c <= cw if i==0 else 0 <= c <= ch for c in [sc2[i][0], sc2[i][1], sc2[i+1][0], sc2[i+1][1]]):
                    draw.line([sc2[i], sc2[i+1]], fill=col, width=width)
        
        # Info text (top-left)
        w_cm = round(dw, 1)
        h_cm = round(dh, 1)
        n_sz = len(parser.graded_polys) if parser.graded_polys else 1
        draw.text((10, 10), f"{w_cm}x{h_cm}cm  zoom{zoom:.1f}x  sizes:{n_sz}", fill=(100, 140, 200))
        
        return img

class PDFExporter:
    def export(self, parser, out_path):
        if not parser.bounds: raise RuntimeError("No geometry")
        b = parser.bounds
        pad, ox, oy = 1.5, -b[0]+1.5, -b[1]+1.5
        pw, ph = (b[2]-b[0]+3)*cm, (b[3]-b[1]+3)*cm
        c = pdf_canvas.Canvas(out_path, pagesize=(pw, ph))
        px, py = lambda x: (x+ox)*cm, lambda y: (y+oy)*cm
        
        # Draw all graded sizes with labels (Desktop App exact)
        if parser.graded_polys and parser.rul_parser:
            for si, sn in enumerate(parser.rul_parser.sizes):
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                c.setLineWidth(0.5 if sn==parser.rul_parser.sample else 0.3)
                c.setStrokeColorRGB(*[v/255 for v in col])
                for poly in parser.graded_polys.get(sn, []):
                    if len(poly) < 2: continue
                    p = c.beginPath()
                    p.moveTo(px(poly[0][0]), py(poly[0][1]))
                    for pt in poly[1:]: p.lineTo(px(pt[0]), py(pt[1]))
                    c.drawPath(p, stroke=1, fill=0)
                    # Size label
                    lx, ly = min(p[0] for p in poly), min(p[1] for p in poly) - 0.7
                    c.setFont("Helvetica-Bold", 7)
                    c.drawString(px(lx), py(ly), f"Size: {sn}")
        
        # Draw other entities (sew, grain, notches, text)
        for ent in parser.entities:
            if ent["layer"]=="7" or len(ent["points"])<2: continue
            if ent["type"] == "TEXT":
                pts = ent["points"]
                c.setFont("Helvetica", 6)
                c.setFillColorRGB(0.5, 0.5, 0.5)
                c.drawString(px(pts[0][0]), py(pts[0][1]), ent.get("text", ""))
                continue
            pts = ent["points"]
            c.setLineWidth(0.3)
            c.setStrokeColorRGB(0,0,0)
            p = c.beginPath()
            p.moveTo(px(pts[0][0]), py(pts[0][1]))
            for pt in pts[1:]: p.lineTo(px(pt[0]), py(pt[1]))
            c.drawPath(p, stroke=1, fill=0)
        c.showPage()
        c.save()

class SVGExporter:
    def export(self, parser, out_path):
        if not parser.bounds: raise RuntimeError("No geometry")
        pts = [(p[0]*10, p[1]*10) for e in (parser.graded_polys[s] for s in parser.graded_polys) for poly in e for p in poly] if parser.graded_polys else [(p[0]*10, p[1]*10) for e in parser.entities for p in e["points"]]
        if not pts: raise RuntimeError("No geometry")
        xs, ys = [p[0] for p in pts], [p[1] for p in pts]
        b = (min(xs), min(ys), max(xs), max(ys))
        pad, x_off, y_off = 15, -b[0]+15, -b[1]+15
        svg_w, svg_h = (b[2]-b[0])+30, (b[3]-b[1])+30
        sx, sy = lambda x: round(x+x_off,3), lambda y: round(svg_h-(y+y_off),3)
        
        lines = [f'<?xml version="1.0" encoding="UTF-8"?><svg xmlns="http://www.w3.org/2000/svg" width="{svg_w:.3f}mm" height="{svg_h:.3f}mm" viewBox="0 0 {svg_w:.3f} {svg_h:.3f}">']
        
        if parser.graded_polys and parser.rul_parser:
            for si, sn in enumerate(parser.rul_parser.sizes):
                col = GRADE_COLORS_HEX[si % len(GRADE_COLORS_HEX)]
                sw = "0.5" if sn==parser.rul_parser.sample else "0.3"
                lines.append(f'<g id="Size_{sn}">')
                for poly in parser.graded_polys.get(sn, []):
                    if len(poly)<2: continue
                    d = "M "+",".join(f"{sx(p[0])},{sy(p[1])}" for p in poly)
                    lines.append(f'<path d="{d}" fill="none" stroke="{col}" stroke-width="{sw}"/>')
                    lx, ly = min(p[0] for p in poly), min(p[1] for p in poly)-7
                    lines.append(f'<text x="{sx(lx)}" y="{sy(ly)}" font-family="Helvetica" font-size="8" fill="{col}">Size: {sn}</text>')
                lines.append('</g>')
        
        # Other entities
        for ent in parser.entities:
            if ent["type"] == "TEXT":
                pts = ent["points"]
                lines.append(f'<text x="{sx(pts[0][0]*10)}" y="{sy(pts[0][1]*10)}" font-family="Helvetica" font-size="6" fill="#888">{ent.get("text", "")}</text>')
                continue
            if len(ent["points"])<2: continue
            d = "M "+",".join(f"{sx(p[0]*10)},{sy(p[1]*10)}" for p in ent["points"])
            lines.append(f'<path d="{d}" fill="none" stroke="#888" stroke-width="0.25"/>')
        
        lines.append('</svg>')
        with open(out_path, 'w') as f: f.write('\n'.join(lines))

@app.route('/api/upload', methods=['POST'])
def upload():
    try:
        file = request.files.get('file')
        if not file or not file.filename: return jsonify({'success': False, 'error': 'No file'}), 400
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], file.filename)
        file.save(filepath)
        parser = AAMAParser()
        parser.parse(filepath)
        active_parser[request.remote_addr] = parser
        img = PreviewRenderer().render(parser, 800, 600, 1.0)
        buf = io.BytesIO()
        img.save(buf, format='PNG')
        b = parser.bounds
        return jsonify({'success': True, 'preview': base64.b64encode(buf.getvalue()).decode(), 'info': f"Width: {round(b[2]-b[0],1) if b else 0}cm\nHeight: {round(b[3]-b[1],1) if b else 0}cm", 'has_grading': bool(parser.graded_polys)})
    except Exception as e: return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/api/upload_rul', methods=['POST'])
def upload_rul():
    try:
        parser = active_parser.get(request.remote_addr)
        if not parser: return jsonify({'success': False, 'error': 'Upload DXF first'}), 400
        file = request.files.get('file')
        if not file: return jsonify({'success': False, 'error': 'No file'}), 400
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], file.filename)
        file.save(filepath)
        rul = RULParser()
        rul.parse(filepath)
        parser.attach_rul(rul)
        img = PreviewRenderer().render(parser, 800, 600, 1.0)
        buf = io.BytesIO()
        img.save(buf, format='PNG')
        return jsonify({'success': True, 'preview': base64.b64encode(buf.getvalue()).decode(), 'sizes': ' '.join(rul.sizes), 'sizes_count': len(rul.sizes)})
    except Exception as e: return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/api/export', methods=['POST'])
def export():
    try:
        parser = active_parser.get(request.remote_addr)
        if not parser: return jsonify({'success': False, 'error': 'No file loaded'}), 400
        fmt = request.get_json().get('format', 'pdf')
        out = os.path.join(app.config['OUTPUT_FOLDER'], f"pattern.{fmt}")
        if fmt == 'pdf': PDFExporter().export(parser, out)
        elif fmt == 'svg': SVGExporter().export(parser, out)
        else: return jsonify({'success': False, 'error': 'Format not supported'}), 400
        return send_file(out, as_attachment=True, download_name=f"pattern.{fmt}")
    except Exception as e: return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/')
def index(): return jsonify({'status': 'API running', 'version': VERSION})

@atexit.register
def cleanup():
    try: shutil.rmtree(UPLOAD_FOLDER); shutil.rmtree(OUTPUT_FOLDER)
    except: pass

if __name__ == '__main__': app.run(debug=True, host='0.0.0.0', port=5000)
