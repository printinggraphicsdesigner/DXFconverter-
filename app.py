"""
Flaremo DXF Converter - Flask Web API
Full Version v2.1 - Optimized for High-Precision Curves and Corners
"""
VERSION = "v2.1"
from flask import Flask, request, jsonify, send_file
from flask_cors import CORS
import os, io, base64, math, re, tempfile, shutil, atexit
from reportlab.pdfgen import canvas as pdf_canvas
from reportlab.lib.units import cm
import ezdxf
from ezdxf import recover as dxf_recover
from ezdxf import path  # High-precision curve calculation
from PIL import Image, ImageDraw

app = Flask(__name__)
CORS(app)
app.config['MAX_CONTENT_LENGTH'] = 50 * 1024 * 1024

UPLOAD_FOLDER = tempfile.mkdtemp()
OUTPUT_FOLDER = tempfile.mkdtemp()
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['OUTPUT_FOLDER'] = OUTPUT_FOLDER

# --- Constants & Colors ---
BG_DARK = "#0A0A0A"
BG_PANEL = "#111111"
BG_CARD = "#1A1A1A"
ACCENT = "#F07800"
ERR = "#FF4444"
TEXT_SEC = "#888888"
BORDER = "#2A2A2A"

LAYER_COLORS = {
    "1": (255, 255, 255), "14": (100, 220, 100), "8": (255, 200, 60),
    "4": (255, 120, 120), "7": (50, 50, 80), "2": (160, 200, 255),
    "13": (200, 150, 255),
}
DEFAULT_COLOR = (79, 142, 247)

GRADE_COLORS = [
    (255, 80, 80), (255, 165, 40), (230, 230, 50), (255, 255, 255),
    (80, 210, 80), (60, 160, 255), (200, 80, 255),
]

GRADE_COLORS_HEX = [
    "#FF5050", "#FFA528", "#C8C800", "#000000",
    "#28B428", "#1E90FF", "#A028FF",
]

active_parser = {}

# --- RUL Parser Class ---
class RULParser:
    def __init__(self):
        self.sizes = []
        self.sample = "M"
        self.sample_idx = 3
        self.rules = {}

    def parse(self, filepath):
        with open(filepath, "rb") as f:
            raw = f.read()
        text = raw.decode("latin-1", errors="replace")
        
        m = re.search(r"SIZE LIST:\s*(.+)", text)
        if m:
            self.sizes = m.group(1).strip().split()
        m = re.search(r"SAMPLE SIZE:\s*(\S+)", text)
        if m:
            self.sample = m.group(1).strip()
        if self.sample in self.sizes:
            self.sample_idx = self.sizes.index(self.sample)
        
        blocks = re.split(r"RULE:\s*DELTA\s+(\d+)", text)
        i = 1
        while i < len(blocks) - 1:
            rnum = int(blocks[i])
            pairs = re.findall(r"(-?\d+\.?\d*),\s*(-?\d+\.?\d*)", blocks[i+1])
            if pairs:
                self.rules[rnum] = [(float(x), float(y)) for x, y in pairs]
            i += 2

    def get_delta_mm(self, rule_num, size_idx):
        if rule_num in self.rules and size_idx < len(self.rules[rule_num]):
            return self.rules[rule_num][size_idx]
        return (0.0, 0.0)

# --- Geometry Utilities ---
def _arc_length(pts, i1, i2):
    total = 0.0
    for k in range(i1, i2):
        dx = pts[k+1][0] - pts[k][0]
        dy = pts[k+1][1] - pts[k][1]
        total += math.hypot(dx, dy)
    return total

def _arc_length_wrap(pts, i1, i2):
    n = len(pts) - 1
    if i2 >= i1:
        return _arc_length(pts, i1, i2)
    else:
        return (_arc_length(pts, i1, n) + _arc_length(pts, 0, i2))

def compute_graded_poly(base_pts, grade_indices, rul, size_idx):
    n = len(base_pts) - 1
    if not grade_indices: return list(base_pts)
    
    grade_deltas = {}
    for gi, rule in grade_indices:
        dx_mm, dy_mm = rul.get_delta_mm(rule, size_idx)
        grade_deltas[gi] = (dx_mm * 0.1, dy_mm * 0.1)
    
    graded = []
    for pi in range(len(base_pts)):
        pt = base_pts[pi]
        pi_mod = pi % n
        if pi_mod in grade_deltas:
            dx, dy = grade_deltas[pi_mod]
            graded.append((pt[0] + dx, pt[1] + dy))
            continue
        
        prev_gi = None
        next_gi = None
        for gi, rule in grade_indices:
            if gi <= pi_mod: prev_gi = gi
        for gi, rule in grade_indices:
            if gi >= pi_mod:
                next_gi = gi
                break
        
        if prev_gi is None: prev_gi = grade_indices[-1][0]
        if next_gi is None: next_gi = grade_indices[0][0]
        
        dx_a, dy_a = grade_deltas[prev_gi]
        dx_b, dy_b = grade_deltas[next_gi]
        
        if prev_gi == next_gi:
            t = 0.0
        elif prev_gi <= pi_mod and pi_mod <= next_gi:
            len_ap = _arc_length(base_pts, prev_gi, pi_mod)
            len_ab = _arc_length(base_pts, prev_gi, next_gi)
            t = len_ap / len_ab if len_ab > 1e-12 else 0.0
        else:
            len_ap = _arc_length_wrap(base_pts, prev_gi, pi_mod)
            len_ab = _arc_length_wrap(base_pts, prev_gi, next_gi)
            t = len_ap / len_ab if len_ab > 1e-12 else 0.0
        
        t = max(0.0, min(1.0, t))
        graded.append((pt[0] + dx_a + t*(dx_b-dx_a), pt[1] + dy_a + t*(dy_b-dy_a)))
    
    return graded

# --- UPDATED AAMA Parser Class (The Core Solution) ---
class AAMAParser:
    def __init__(self):
        self.entities = []
        self.bounds = None
        self.unit_name = "mm→cm"
        self.scale = 0.1
        self.metadata = {}
        self.grade_indices = []
        self.rul_parser = None
        self.graded_polys = {}
        self._base_cut_polys = []

    def parse(self, filepath):
        self.entities = []
        self.metadata = {}
        self.grade_indices = []
        self.graded_polys = {}
        self._base_cut_polys = []
        
        try:
            doc, _ = dxf_recover.readfile(filepath)
            msp = doc.modelspace()
            
            # Smart Scale Detection
            extents = msp.get_bounding_box()
            rw = extents[1].x - extents[0].x
            self.scale = 0.1 if rw > 20 else 1.0

            # Step 1: Collect Point Rules for Grading
            point_rules = {}
            for ent in msp:
                if ent.dxftype() == "TEXT" and str(ent.dxf.layer) == "1":
                    txt = ent.dxf.text.strip()
                    if txt.startswith("#"):
                        # High precision key for matching
                        key = (round(ent.dxf.insert.x * self.scale, 5), 
                               round(ent.dxf.insert.y * self.scale, 5))
                        try:
                            point_rules[key] = int(txt[1:])
                        except: pass

            # Step 2: Process Entities with Path API for Perfect Curves
            for ent in msp:
                t = ent.dxftype()
                lay = str(getattr(ent.dxf, "layer", "1"))

                if t in ("LWPOLYLINE", "POLYLINE", "SPLINE", "ARC", "CIRCLE", "LINE"):
                    try:
                        # Path API handles bulges and splines perfectly
                        p = path.make_path(ent)
                        # distance=0.005 ensures smooth curves and sharp corners
                        pts = [(pt.x * self.scale, pt.y * self.scale) 
                               for pt in p.flattening(distance=0.005)]
                        
                        if pts:
                            self._add(t, pts, lay)
                            if lay == "1":
                                self._base_cut_polys.append(pts)
                                # Identify grade indices based on text markers
                                gi = []
                                for vi, pt in enumerate(pts[:-1]):
                                    pk = (round(pt[0], 5), round(pt[1], 5))
                                    if pk in point_rules:
                                        gi.append((vi, point_rules[pk]))
                                if gi and not self.grade_indices:
                                    self.grade_indices = gi
                    except: continue

                elif t in ("TEXT", "MTEXT"):
                    self._parse_meta_entity(ent)

            self._update_bounds()
        except Exception as e:
            raise RuntimeError(f"DXF read error: {e}")

    def _add(self, etype, pts, layer):
        # 6-decimal precision prevents corner shifting
        pts = [(round(p[0], 6), round(p[1], 6)) for p in pts]
        self.entities.append({
            "type": etype, "points": pts, "layer": layer,
            "color": LAYER_COLORS.get(layer, DEFAULT_COLOR)
        })

    def _parse_meta_entity(self, ent):
        try:
            txt = ent.dxf.text if ent.dxftype() == "TEXT" else ent.plain_mtext()
            txt = txt.strip()
            if not txt or txt.startswith("#"): return
            
            # Map metadata
            for label, key in [("Style Name", "style"), ("Piece Name", "piece"), ("Size", "size")]:
                if txt.startswith(label + ": "):
                    self.metadata[key] = txt.split(": ", 1)[1].strip()

            pos = ent.dxf.insert
            self.entities.append({
                "type": "TEXT", "points": [(pos.x*self.scale, pos.y*self.scale)],
                "text": txt, "layer": str(ent.dxf.layer), "color": DEFAULT_COLOR
            })
        except: pass

    def attach_rul(self, rul):
        self.rul_parser = rul
        if not self._base_cut_polys or not rul.sizes: return
        for size_idx, size_name in enumerate(rul.sizes):
            self.graded_polys[size_name] = [compute_graded_poly(bp, self.grade_indices, rul, size_idx) 
                                            for bp in self._base_cut_polys]
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

# --- Preview Renderer Class ---
class PreviewRenderer:
    BG = (13, 15, 20); GRID_MAJ = (35, 42, 65); GRID_MIN = (20, 26, 44)
    RULER_BG = (18, 22, 38); RULER_FG = (110, 140, 200)

    def render(self, parser, cw, ch, zoom=1.0, pan_x=0.0, pan_y=0.0):
        img = Image.new("RGB", (cw, ch), self.BG)
        draw = ImageDraw.Draw(img)
        if not parser.entities or not parser.bounds: return img
        
        b = parser.bounds
        dw, dh = max(b[2]-b[0], 1), max(b[3]-b[1], 1)
        RULER = 40
        aw, ah = cw-RULER, ch-RULER
        scale = min(aw/dw, ah/dh) * 0.9 * zoom
        cx, cy = RULER + aw/2 + pan_x, RULER + ah/2 + pan_y
        mxc, myc = (b[0]+b[2])/2, (b[1]+b[3])/2
        
        def tx(x): return cx + (x-mxc)*scale
        def ty(y): return cy - (y-myc)*scale

        # Grid logic
        for step, col in [(1, self.GRID_MIN), (10, self.GRID_MAJ)]:
            gx = math.floor(b[0]/step)*step
            while gx <= b[2]+step:
                sx = int(tx(gx))
                if RULER <= sx <= cw: draw.line([(sx, RULER), (sx, ch)], fill=col)
                gx += step

        # Draw Graded Polys
        if parser.graded_polys:
            for si, sname in enumerate(parser.rul_parser.sizes):
                if sname == parser.rul_parser.sample: continue
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                for poly in parser.graded_polys.get(sname, []):
                    draw.line([(int(tx(p[0])), int(ty(p[1]))) for p in poly], fill=col, width=1)

        # Draw Entities
        for ent in parser.entities:
            if ent["type"] == "TEXT":
                draw.text((int(tx(ent["points"][0][0])), int(ty(ent["points"][0][1]))), 
                          ent["text"][:30], fill=ent["color"])
            elif len(ent["points"]) > 1:
                lw = 2 if ent["layer"] == "1" else 1
                draw.line([(int(tx(p[0])), int(ty(p[1]))) for p in ent["points"]], 
                          fill=ent["color"], width=lw)
        return img

# --- Exporters ---
class ActualSizePDFExporter:
    def export(self, parser, out_path):
        b = parser.bounds
        pad = 2.0
        ox, oy = -b[0]+pad, -b[1]+pad
        pw, ph = (b[2]-b[0]+2*pad)*cm, (b[3]-b[1]+2*pad)*cm
        c = pdf_canvas.Canvas(out_path, pagesize=(pw, ph))
        
        def px(x): return (x+ox)*cm
        def py(y): return (y+oy)*cm

        for ent in parser.entities:
            if ent["type"] == "TEXT": continue
            c.setLineWidth(0.3 if ent["layer"] != "1" else 0.5)
            pts = ent["points"]
            p = c.beginPath()
            p.moveTo(px(pts[0][0]), py(pts[0][1]))
            for pt in pts[1:]: p.lineTo(px(pt[0]), py(pt[1]))
            c.drawPath(p)
        
        if parser.graded_polys:
            for si, sname in enumerate(parser.rul_parser.sizes):
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                c.setStrokeColorRGB(col[0]/255, col[1]/255, col[2]/255)
                for poly in parser.graded_polys[sname]:
                    p = c.beginPath()
                    p.moveTo(px(poly[0][0]), py(poly[0][1]))
                    for pt in poly[1:]: p.lineTo(px(pt[0]), py(pt[1]))
                    c.drawPath(p)
        c.save()

class SVGExporter:
    def export(self, parser, out_path):
        b = parser.bounds
        pad = 10.0
        svg_w = (b[2]-b[0])*10 + 2*pad
        svg_h = (b[3]-b[1])*10 + 2*pad
        with open(out_path, 'w') as f:
            f.write(f'<svg width="{svg_w}mm" height="{svg_h}mm" viewBox="0 0 {svg_w} {svg_h}" xmlns="http://www.w3.org/2000/svg">')
            for ent in parser.entities:
                if ent["type"] == "TEXT": continue
                d = "M " + " L ".join([f"{(p[0]-b[0])*10+pad},{(svg_h-(p[1]-b[1])*10-pad)}" for p in ent["points"]])
                f.write(f'<path d="{d}" stroke="black" fill="none" stroke-width="0.5"/>')
            f.write('</svg>')

# --- Flask Routes ---
@app.route('/api/upload', methods=['POST'])
def upload():
    try:
        file = request.files['file']
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], file.filename)
        file.save(filepath)
        parser = AAMAParser()
        parser.parse(filepath)
        active_parser[request.remote_addr] = parser
        img = PreviewRenderer().render(parser, 800, 600)
        buf = io.BytesIO(); img.save(buf, format='PNG')
        return jsonify({'success': True, 'preview': base64.b64encode(buf.getvalue()).decode(), 
                        'info': f"W: {round(parser.bounds[2]-parser.bounds[0],2)}cm H: {round(parser.bounds[3]-parser.bounds[1],2)}cm"})
    except Exception as e: return jsonify({'success': False, 'error': str(e)})

@app.route('/api/upload_rul', methods=['POST'])
def upload_rul():
    try:
        sid = request.remote_addr
        file = request.files['file']
        path_rul = os.path.join(app.config['UPLOAD_FOLDER'], file.filename)
        file.save(path_rul)
        rul = RULParser(); rul.parse(path_rul)
        active_parser[sid].attach_rul(rul)
        img = PreviewRenderer().render(active_parser[sid], 800, 600)
        buf = io.BytesIO(); img.save(buf, format='PNG')
        return jsonify({'success': True, 'preview': base64.b64encode(buf.getvalue()).decode()})
    except Exception as e: return jsonify({'success': False, 'error': str(e)})

@app.route('/api/export', methods=['POST'])
def export():
    data = request.json
    fmt = data.get('format', 'pdf')
    parser = active_parser.get(request.remote_addr)
    out_name = f"output.{fmt}"
    out_path = os.path.join(app.config['OUTPUT_FOLDER'], out_name)
    if fmt == 'pdf': ActualSizePDFExporter().export(parser, out_path)
    else: SVGExporter().export(parser, out_path)
    return send_file(out_path, as_attachment=True)

@app.route('/')
def index(): return jsonify({'status': 'running', 'version': VERSION})

@atexit.register
def cleanup():
    shutil.rmtree(UPLOAD_FOLDER, ignore_errors=True)
    shutil.rmtree(OUTPUT_FOLDER, ignore_errors=True)

if __name__ == '__main__':
    app.run(debug=True, host='0.0.0.0', port=5000)
