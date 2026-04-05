"""
╔══════════════════════════════════════════════════════════╗
║   Flaremo DXF Converter - CLO Compatible                 ║
║   Clean Output - No Desktop App Reference                ║
║   Smooth Curves, Clean Preview, Accurate Grading         ║
╚══════════════════════════════════════════════════════════╝
"""
VERSION = "v5.0"
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

# ═══════════════════════════════════════════════
# COLORS (Clean, CLO-style)
# ═══════════════════════════════════════════════
LAYER_COLORS = {
    "1": (255, 255, 255),   # Cut line - white
    "14": (100, 220, 100),  # Sew line - green
    "8": (255, 200, 60),    # Grain - gold
    "4": (255, 120, 120),   # Notch - red
}
DEFAULT_COLOR = (255, 255, 255)

GRADE_COLORS = [
    (255, 80, 80),    # Red
    (255, 165, 40),   # Orange
    (230, 230, 50),   # Yellow
    (255, 255, 255),  # White (base)
    (80, 210, 80),    # Green
    (60, 160, 255),   # Blue
    (200, 80, 255),   # Purple
]

GRADE_COLORS_HEX = [
    "#FF5050", "#FFA528", "#E6E632", "#FFFFFF",
    "#50D250", "#3CA0FF", "#C850FF",
]

active_parser = {}

# ═══════════════════════════════════════════════
# RUL PARSER (Standard)
# ═══════════════════════════════════════════════
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

# ═══════════════════════════════════════════════
# GRADING ENGINE (Arc-length interpolation)
# ═══════════════════════════════════════════════
def _arc_length(pts, i1, i2):
    total = 0.0
    for k in range(i1, i2):
        dx = pts[k+1][0] - pts[k][0]
        dy = pts[k+1][1] - pts[k][1]
        total += math.hypot(dx, dy)
    return total

def compute_graded_poly(base_pts, grade_indices, rul, size_idx):
    n = len(base_pts) - 1
    if len(grade_indices) == 0:
        return list(base_pts)
    
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
        
        # Find surrounding grade points
        prev_gi = next_gi = None
        for gi, rule in grade_indices:
            if gi <= pi_mod:
                prev_gi = gi
        for gi, rule in grade_indices:
            if gi >= pi_mod:
                next_gi = gi
                break
        
        if prev_gi is None:
            prev_gi = grade_indices[-1][0]
        if next_gi is None:
            next_gi = grade_indices[0][0]
        
        dx_a, dy_a = grade_deltas[prev_gi]
        dx_b, dy_b = grade_deltas[next_gi]
        
        if prev_gi == next_gi:
            t = 0.0
        else:
            len_ap = _arc_length(base_pts, prev_gi, pi_mod)
            len_ab = _arc_length(base_pts, prev_gi, next_gi)
            t = len_ap / len_ab if len_ab > 1e-9 else 0.0
        
        t = max(0.0, min(1.0, t))
        dx = dx_a + t * (dx_b - dx_a)
        dy = dy_a + t * (dy_b - dy_a)
        graded.append((pt[0] + dx, pt[1] + dy))
    
    return graded

# ═══════════════════════════════════════════════
# DXF PARSER - CLEAN (CLO-style)
# ═══════════════════════════════════════════════
class AAMAParser:
    def __init__(self):
        self.entities = []
        self.bounds = None
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
        except Exception as e:
            raise RuntimeError(f"DXF read error: {e}")

        msp = doc.modelspace()
        
        # Parse blocks (pattern pieces)
        for ent in msp:
            if ent.dxftype() == "INSERT":
                block = doc.blocks.get(ent.dxf.name)
                if block:
                    self._parse_block(block)
        
        # Fallback: direct entities
        if not self.entities:
            self._parse_entities(msp)

        self._update_bounds()

    def _parse_block(self, block):
        # Determine scale
        raw_xs = []
        for ent in block:
            if ent.dxftype() in ("POLYLINE", "LINE"):
                if ent.dxftype() == "POLYLINE":
                    for v in ent.vertices:
                        raw_xs.append(v.dxf.location.x)
                else:
                    raw_xs += [ent.dxf.start.x, ent.dxf.end.x]
        
        if not raw_xs:
            return
        
        rw = max(raw_xs) - min(raw_xs)
        sc = 0.1 if rw > 200 else 1.0  # mm to cm
        self.scale = sc

        # Collect grade points (#1, #2, etc.)
        point_rules = {}
        for ent in block:
            if ent.dxftype() == "TEXT":
                txt = ent.dxf.text.strip()
                m = re.match(r"^#\s*(\d+)$", txt)
                if m and str(ent.dxf.layer) == "1":
                    pos = ent.dxf.insert
                    key = (round(pos.x*sc, 3), round(pos.y*sc, 3))
                    point_rules[key] = int(m.group(1))

        # Parse geometry - CLEAN, only essential entities
        for ent in block:
            t = ent.dxftype()
            lay = str(getattr(ent.dxf, "layer", "1"))

            if t == "POLYLINE":
                verts = list(ent.vertices)
                pts = [(v.dxf.location.x*sc, v.dxf.location.y*sc) for v in verts]
                if ent.is_closed and pts and pts[0] != pts[-1]:
                    pts.append(pts[0])
                if pts:
                    self._add("POLYLINE", pts, lay)
                    if lay == "1":
                        self._base_cut_polys.append(pts)
                        # Build grade indices
                        gi = []
                        for vi, pt in enumerate(pts[:-1]):
                            key = (round(pt[0], 3), round(pt[1], 3))
                            if key in point_rules:
                                gi.append((vi, point_rules[key]))
                        if gi and not self.grade_indices:
                            self.grade_indices = gi

            elif t == "LWPOLYLINE":
                pts = [(p[0]*sc, p[1]*sc) for p in ent.get_points()]
                if ent.closed and pts and pts[0] != pts[-1]:
                    pts.append(pts[0])
                if pts:
                    self._add("LWPOLYLINE", pts, lay)
                    if lay == "1" and not self._base_cut_polys:
                        self._base_cut_polys.append(pts)

            elif t == "SPLINE":
                # CLO Compatible: tolerance 0.01 for smooth curves
                try:
                    pts = [(p[0]*sc, p[1]*sc) for p in ent.flattening(0.01)]
                    if pts:
                        self._add("SPLINE", pts, lay)
                except:
                    pass

            elif t == "LINE":
                s, e = ent.dxf.start, ent.dxf.end
                self._add("LINE", [(s.x*sc, s.y*sc), (e.x*sc, e.y*sc)], lay)

            elif t == "ARC":
                # Dynamic steps for smooth curves
                pts = self._arc_pts(ent, sc)
                if pts:
                    self._add("ARC", pts, lay)

            elif t == "CIRCLE":
                cx, cy = ent.dxf.center.x*sc, ent.dxf.center.y*sc
                r = ent.dxf.radius*sc
                self._add("CIRCLE", self._circle_pts(cx, cy, r), lay)

    def _parse_entities(self, container):
        raw_xs = []
        for ent in container:
            if ent.dxftype() == "LWPOLYLINE":
                for p in ent.get_points():
                    raw_xs.append(p[0])
        
        sc = 0.1 if (raw_xs and max(raw_xs) > 200) else 1.0
        self.scale = sc
        
        for ent in container:
            t = ent.dxftype()
            lay = str(getattr(ent.dxf, "layer", "1"))
            if t == "LINE":
                s, e = ent.dxf.start, ent.dxf.end
                self._add("LINE", [(s.x*sc, s.y*sc), (e.x*sc, e.y*sc)], lay)
            elif t == "LWPOLYLINE":
                pts = [(p[0]*sc, p[1]*sc) for p in ent.get_points()]
                if pts:
                    self._add("LWPOLYLINE", pts, lay)
            elif t == "SPLINE":
                try:
                    pts = [(p[0]*sc, p[1]*sc) for p in ent.flattening(0.01)]
                    if pts:
                        self._add("SPLINE", pts, lay)
                except:
                    pass

    def attach_rul(self, rul):
        self.rul_parser = rul
        self.graded_polys = {}
        
        if not self._base_cut_polys or not rul.sizes:
            return
        
        for size_idx, size_name in enumerate(rul.sizes):
            graded_polys_for_size = []
            for base_poly in self._base_cut_polys:
                gp = compute_graded_poly(base_poly, self.grade_indices, rul, size_idx)
                graded_polys_for_size.append(gp)
            self.graded_polys[size_name] = graded_polys_for_size
        
        self._update_bounds(include_graded=True)

    def _update_bounds(self, include_graded=False):
        xs, ys = [], []
        for e in self.entities:
            for p in e["points"]:
                xs.append(p[0])
                ys.append(p[1])
        if include_graded:
            for polys in self.graded_polys.values():
                for poly in polys:
                    for p in poly:
                        xs.append(p[0])
                        ys.append(p[1])
        if xs:
            self.bounds = (min(xs), min(ys), max(xs), max(ys))

    def _add(self, etype, pts, layer):
        self.entities.append({
            "type": etype,
            "points": pts,
            "layer": layer,
            "color": LAYER_COLORS.get(layer, DEFAULT_COLOR)
        })

    def _arc_pts(self, arc, sc, min_steps=128):
        """Dynamic steps for smooth arcs (CLO-style)"""
        try:
            cx, cy = arc.dxf.center.x*sc, arc.dxf.center.y*sc
            r = arc.dxf.radius*sc
            sa = math.radians(arc.dxf.start_angle)
            ea = math.radians(arc.dxf.end_angle)
            if ea < sa:
                ea += 2*math.pi
            
            arc_len_mm = r * (ea - sa) * 10
            steps = max(min_steps, int(arc_len_mm * 2))
            
            return [(cx+r*math.cos(sa+(ea-sa)*i/steps),
                     cy+r*math.sin(sa+(ea-sa)*i/steps))
                    for i in range(steps+1)]
        except:
            return []

    def _circle_pts(self, cx, cy, r, min_steps=256):
        """Dynamic steps for smooth circles (CLO-style)"""
        circ_mm = 2 * math.pi * r * 10
        steps = max(min_steps, int(circ_mm * 2))
        
        return [(cx+r*math.cos(2*math.pi*i/steps),
                 cy+r*math.sin(2*math.pi*i/steps))
                for i in range(steps+1)]

# ═══════════════════════════════════════════════
# PREVIEW RENDERER - CLEAN (CLO-style)
# ═══════════════════════════════════════════════
class PreviewRenderer:
    BG = (13, 13, 18)  # Dark background like CLO
    
    def render(self, parser, cw, ch, zoom=1.0):
        img = Image.new("RGB", (cw, ch), self.BG)
        draw = ImageDraw.Draw(img)
        
        if not parser.entities or not parser.bounds:
            return img
        
        b = parser.bounds
        dw = (b[2]-b[0]) or 1
        dh = (b[3]-b[1]) or 1
        
        # Calculate scale and center
        margin = 60
        aw = cw - 2*margin
        ah = ch - 2*margin
        base = min(aw/dw, ah/dh) * 0.90
        scale = base * zoom
        
        cx = cw/2
        cy = ch/2
        mxc = (b[0]+b[2])/2
        myc = (b[1]+b[3])/2
        
        def tx(x): return cx + (x-mxc)*scale
        def ty(y): return cy - (y-myc)*scale  # Flip Y
        
        # Draw graded sizes (thin, colored lines)
        if parser.graded_polys and parser.rul_parser:
            sizes = parser.rul_parser.sizes
            sample = parser.rul_parser.sample
            
            for si, sname in enumerate(sizes):
                polys = parser.graded_polys.get(sname, [])
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                width = 2 if sname == sample else 1
                
                for poly_pts in polys:
                    if len(poly_pts) < 2:
                        continue
                    sc2 = [(int(tx(p[0])), int(ty(p[1]))) for p in poly_pts]
                    for i in range(len(sc2)-1):
                        x1, y1 = sc2[i]
                        x2, y2 = sc2[i+1]
                        if 0 <= x1,x2 <= cw and 0 <= y1,y2 <= ch:
                            draw.line([(x1, y1), (x2, y2)], fill=col, width=width)
        
        # Draw base entities (sew lines, grain, notches)
        for ent in parser.entities:
            pts = ent["points"]
            lay = ent.get("layer", "1")
            col = ent.get("color", DEFAULT_COLOR)
            
            if len(pts) < 2:
                continue
            
            width = 1 if lay == "1" else 1
            sc2 = [(int(tx(p[0])), int(ty(p[1]))) for p in pts]
            
            for i in range(len(sc2)-1):
                x1, y1 = sc2[i]
                x2, y2 = sc2[i+1]
                if 0 <= x1,x2 <= cw and 0 <= y1,y2 <= ch:
                    draw.line([(x1, y1), (x2, y2)], fill=col, width=width)
        
        # Info text (top-left, clean)
        w_cm = round(dw, 1)
        h_cm = round(dh, 1)
        n_sz = len(parser.graded_polys) if parser.graded_polys else 1
        draw.text((10, 10), f"{w_cm}x{h_cm}cm  zoom{zoom:.1f}x  sizes:{n_sz}",
                  fill=(100, 140, 200))
        
        return img

# ═══════════════════════════════════════════════
# EXPORTERS (Clean, CLO-compatible)
# ═══════════════════════════════════════════════
class PDFExporter:
    def export(self, parser, out_path):
        if not parser.bounds:
            raise RuntimeError("No geometry")
        
        b = parser.bounds
        pad = 1.5
        ox = -b[0]+pad
        oy = -b[1]+pad
        pw = (b[2]-b[0]+2*pad)*cm
        ph = (b[3]-b[1]+2*pad)*cm
        
        c = pdf_canvas.Canvas(out_path, pagesize=(pw, ph))
        c.setTitle("Pattern - Actual Size 1:1")
        
        def px(x): return (x+ox)*cm
        def py(y): return (y+oy)*cm
        
        # Draw all graded sizes
        if parser.graded_polys and parser.rul_parser:
            sizes = parser.rul_parser.sizes
            for si, sname in enumerate(sizes):
                polys = parser.graded_polys.get(sname, [])
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                c.setLineWidth(0.5 if sname == parser.rul_parser.sample else 0.3)
                c.setStrokeColorRGB(col[0]/255, col[1]/255, col[2]/255)
                
                for poly_pts in polys:
                    if len(poly_pts) < 2:
                        continue
                    p = c.beginPath()
                    p.moveTo(px(poly_pts[0][0]), py(poly_pts[0][1]))
                    for pt in poly_pts[1:]:
                        p.lineTo(px(pt[0]), py(pt[1]))
                    c.drawPath(p, stroke=1, fill=0)
                    
                    # Size label
                    gxs = [pt[0] for pt in poly_pts]
                    gys = [pt[1] for pt in poly_pts]
                    lx = min(gxs)
                    ly = min(gys) - 0.7
                    c.setFont("Helvetica-Bold", 7)
                    c.drawString(px(lx), py(ly), f"Size: {sname}")
        
        # Draw other entities
        for ent in parser.entities:
            lay = ent.get("layer", "1")
            if lay == "7":
                continue
            pts = ent["points"]
            if len(pts) < 2:
                continue
            c.setLineWidth(0.3)
            c.setStrokeColorRGB(0, 0, 0)
            p = c.beginPath()
            p.moveTo(px(pts[0][0]), py(pts[0][1]))
            for pt in pts[1:]:
                p.lineTo(px(pt[0]), py(pt[1]))
            c.drawPath(p, stroke=1, fill=0)
        
        c.showPage()
        c.save()

class SVGExporter:
    def export(self, parser, out_path):
        if not parser.bounds:
            raise RuntimeError("No geometry")
        
        if parser.graded_polys and parser.rul_parser:
            self._export_graded(parser, out_path)
        else:
            self._export_base(parser, out_path)
    
    def _export_graded(self, parser, out_path):
        rul = parser.rul_parser
        sizes = rul.sizes
        
        # Collect all points
        all_mm = {}
        for sname in sizes:
            polys = parser.graded_polys.get(sname, [])
            all_mm[sname] = [[(p[0]*10, p[1]*10) for p in poly] for poly in polys]
        
        all_pts = [p for polys in all_mm.values() for poly in polys for p in poly]
        if not all_pts:
            raise RuntimeError("No geometry")
        
        xs = [p[0] for p in all_pts]
        ys = [p[1] for p in all_pts]
        b = (min(xs), min(ys), max(xs), max(ys))
        
        pad = 15.0
        x_off = -b[0] + pad
        y_off = -b[1] + pad
        svg_w = (b[2]-b[0]) + 2*pad
        svg_h = (b[3]-b[1]) + 2*pad
        
        def sx(x): return round(x + x_off, 3)
        def sy(y): return round(svg_h - (y + y_off), 3)
        
        lines = [
            '<?xml version="1.0" encoding="UTF-8"?>',
            f'<svg xmlns="http://www.w3.org/2000/svg"',
            f'    width="{svg_w:.3f}mm" height="{svg_h:.3f}mm"',
            f'    viewBox="0 0 {svg_w:.3f} {svg_h:.3f}">',
            ''
        ]
        
        for si, sname in enumerate(sizes):
            polys = all_mm[sname]
            col = GRADE_COLORS_HEX[si % len(GRADE_COLORS_HEX)]
            sw = "0.5" if sname == parser.rul_parser.sample else "0.3"
            
            lines.append(f'  <g id="Size_{sname}">')
            
            for poly in polys:
                if len(poly) < 2:
                    continue
                d = f"M {sx(poly[0][0])},{sy(poly[0][1])}"
                for pt in poly[1:]:
                    d += f" L {sx(pt[0])},{sy(pt[1])}"
                lines.append(f'    <path d="{d}" fill="none" stroke="{col}" stroke-width="{sw}"/>')
                
                # Size label
                gxs = [p[0] for p in poly]
                gys = [p[1] for p in poly]
                lx = min(gxs)
                ly = min(gys) - 7
                lines.append(f'    <text x="{sx(lx)}" y="{sy(ly)}"')
                lines.append(f'          font-family="Helvetica,Arial,sans-serif"')
                lines.append(f'          font-weight="bold" font-size="8" fill="{col}">')
                lines.append(f'      Size: {sname}')
                lines.append(f'    </text>')
            
            lines.append(f'  </g>')
            lines.append('')
        
        lines.append('</svg>')
        
        with open(out_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))
    
    def _export_base(self, parser, out_path):
        all_pts = []
        for e in parser.entities:
            for p in e["points"]:
                all_pts.append((p[0]*10, p[1]*10))
        
        if not all_pts:
            raise RuntimeError("No geometry")
        
        xs = [p[0] for p in all_pts]
        ys = [p[1] for p in all_pts]
        b = (min(xs), min(ys), max(xs), max(ys))
        
        pad = 15.0
        x_off = -b[0] + pad
        y_off = -b[1] + pad
        svg_w = (b[2]-b[0]) + 2*pad
        svg_h = (b[3]-b[1]) + 2*pad
        
        def sx(x): return round(x + x_off, 3)
        def sy(y): return round(svg_h - (y + y_off), 3)
        
        lines = [
            '<?xml version="1.0" encoding="UTF-8"?>',
            f'<svg xmlns="http://www.w3.org/2000/svg"',
            f'    width="{svg_w:.3f}mm" height="{svg_h:.3f}mm"',
            f'    viewBox="0 0 {svg_w:.3f} {svg_h:.3f}">',
            '  <g id="Base">',
        ]
        
        for ent in parser.entities:
            pts = ent["points"]
            if len(pts) < 2:
                continue
            d = f"M {sx(pts[0][0])},{sy(pts[0][1])}"
            for pt in pts[1:]:
                d += f" L {sx(pt[0])},{sy(pt[1])}"
            lines.append(f'    <path d="{d}" fill="none" stroke="#000" stroke-width="0.5"/>')
        
        lines.append('  </g>')
        lines.append('</svg>')
        
        with open(out_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))

# ═══════════════════════════════════════════════
# API ROUTES
# ═══════════════════════════════════════════════
@app.route('/api/upload', methods=['POST'])
def upload():
    try:
        if 'file' not in request.files:
            return jsonify({'success': False, 'error': 'No file'}), 400
        
        file = request.files['file']
        if file.filename == '':
            return jsonify({'success': False, 'error': 'No file selected'}), 400
        
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], file.filename)
        file.save(filepath)
        
        parser = AAMAParser()
        parser.parse(filepath)
        
        session_id = request.remote_addr
        active_parser[session_id] = parser
        
        img = PreviewRenderer().render(parser, 800, 600, 1.0)
        buffer = io.BytesIO()
        img.save(buffer, format='PNG')
        preview_b64 = base64.b64encode(buffer.getvalue()).decode()
        
        b = parser.bounds
        w = round(b[2]-b[0], 1) if b else 0
        h = round(b[3]-b[1], 1) if b else 0
        
        return jsonify({
            'success': True,
            'preview': preview_b64,
            'info': f"Width: {w} cm\nHeight: {h} cm",
            'has_grading': len(parser.graded_polys) > 0
        })
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/api/upload_rul', methods=['POST'])
def upload_rul():
    try:
        session_id = request.remote_addr
        if session_id not in active_parser:
            return jsonify({'success': False, 'error': 'Upload DXF first'}), 400
        
        file = request.files['file']
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], file.filename)
        file.save(filepath)
        
        rul = RULParser()
        rul.parse(filepath)
        
        parser = active_parser[session_id]
        parser.attach_rul(rul)
        
        img = PreviewRenderer().render(parser, 800, 600, 1.0)
        buffer = io.BytesIO()
        img.save(buffer, format='PNG')
        preview_b64 = base64.b64encode(buffer.getvalue()).decode()
        
        return jsonify({
            'success': True,
            'preview': preview_b64,
            'sizes': ' '.join(rul.sizes),
            'sizes_count': len(rul.sizes)
        })
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/api/export', methods=['POST'])
def export():
    try:
        session_id = request.remote_addr
        if session_id not in active_parser:
            return jsonify({'success': False, 'error': 'No file loaded'}), 400
        
        data = request.get_json()
        format_type = data.get('format', 'pdf')
        
        parser = active_parser[session_id]
        output_filename = f"pattern.{format_type}"
        output_path = os.path.join(app.config['OUTPUT_FOLDER'], output_filename)
        
        if format_type == 'pdf':
            PDFExporter().export(parser, output_path)
        elif format_type == 'svg':
            SVGExporter().export(parser, output_path)
        else:
            return jsonify({'success': False, 'error': 'Format not supported'}), 400
        
        return send_file(output_path, as_attachment=True, download_name=output_filename)
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/')
def index():
    return jsonify({'status': 'API running', 'version': VERSION})

@atexit.register
def cleanup():
    try:
        shutil.rmtree(UPLOAD_FOLDER)
        shutil.rmtree(OUTPUT_FOLDER)
    except:
        pass

if __name__ == '__main__':
    app.run(debug=True, host='0.0.0.0', port=5000)
