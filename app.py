"""
Flaremo DXF Converter - Complete Flask Web API
With Full Grading Support
"""
VERSION = "v2.0"
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

LAYER_COLORS = {
    "1": (255, 255, 255), "14": (100, 220, 100), "8": (255, 200, 60),
    "4": (255, 120, 120), "7": (50, 50, 80), "2": (160, 200, 255),
    "13": (200, 150, 255),
}
DEFAULT_COLOR = (79, 142, 247)
GRADE_COLORS = [
    (255, 80, 80), (255, 165, 40), (230, 230, 50),
    (255, 255, 255), (80, 210, 80), (60, 160, 255), (200, 80, 255),
]

active_parser = {}

# RUL Parser
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

# Grading Engine
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
    n_grades = len(grade_indices)
    if n_grades == 0:
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
        prev_gi = None
        next_gi = None
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
        elif prev_gi <= pi_mod and pi_mod <= next_gi:
            len_ap = _arc_length(base_pts, prev_gi, pi_mod)
            len_ab = _arc_length(base_pts, prev_gi, next_gi)
            t = len_ap / len_ab if len_ab > 1e-9 else 0.0
        else:
            len_ap = _arc_length_wrap(base_pts, prev_gi, pi_mod)
            len_ab = _arc_length_wrap(base_pts, prev_gi, next_gi)
            t = len_ap / len_ab if len_ab > 1e-9 else 0.0
        t = max(0.0, min(1.0, t))
        dx = dx_a + t * (dx_b - dx_a)
        dy = dy_a + t * (dy_b - dy_a)
        graded.append((pt[0] + dx, pt[1] + dy))
    return graded

# DXF Parser
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
        for ent in msp:
            if ent.dxftype() == "TEXT":
                try:
                    self._parse_meta(ent.dxf.text.strip())
                except:
                    pass
            elif ent.dxftype() == "INSERT":
                block = doc.blocks.get(ent.dxf.name)
                if block:
                    self._parse_block(block)
        if not self.entities:
            self._parse_entities(msp)
        self._update_bounds()

    def _parse_block(self, block):
        raw_xs = []
        for ent in block:
            if ent.dxftype() == "POLYLINE":
                for v in ent.vertices:
                    raw_xs.append(v.dxf.location.x)
            elif ent.dxftype() == "LINE":
                raw_xs += [ent.dxf.start.x, ent.dxf.end.x]
        if not raw_xs:
            return
        rw = max(raw_xs) - min(raw_xs)
        sc = 0.1 if rw > 20 else 1.0
        self.scale = sc
        point_rules = {}
        for ent in block:
            if ent.dxftype() == "TEXT":
                txt = ent.dxf.text.strip()
                m = re.match(r"^#\s*(\d+)$", txt)
                if m and str(ent.dxf.layer) == "1":
                    pos = ent.dxf.insert
                    key = (round(pos.x*sc, 3), round(pos.y*sc, 3))
                    point_rules[key] = int(m.group(1))
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
            elif t == "LINE":
                s, e = ent.dxf.start, ent.dxf.end
                self._add("LINE", [(s.x*sc, s.y*sc), (e.x*sc, e.y*sc)], lay)
            elif t == "ARC":
                pts = self._arc_pts(ent, sc)
                if pts:
                    self._add("ARC", pts, lay)
            elif t == "CIRCLE":
                cx, cy = ent.dxf.center.x*sc, ent.dxf.center.y*sc
                r = ent.dxf.radius*sc
                self._add("CIRCLE", self._circle_pts(cx, cy, r), lay)
            elif t in ("TEXT", "MTEXT"):
                try:
                    pos = ent.dxf.insert
                    txt = ent.dxf.text if t == "TEXT" else ent.plain_mtext()
                    txt = txt.strip()
                    px, py = pos.x*sc, pos.y*sc
                    if txt and not re.match(r"^#\s*\d+$", txt):
                        h = max(getattr(ent.dxf, "height", 3)*sc, 0.2)
                        self.entities.append({
                            "type": "TEXT", "points": [(px, py)],
                            "text": txt, "height": h, "layer": lay,
                            "color": LAYER_COLORS.get(lay, DEFAULT_COLOR)
                        })
                except:
                    pass

    def _parse_entities(self, container):
        raw_xs = []
        for ent in container:
            if ent.dxftype() == "LWPOLYLINE":
                for p in ent.get_points():
                    raw_xs.append(p[0])
        sc = 0.1 if (raw_xs and max(raw_xs) > 20) else 1.0
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
            "type": etype, "points": pts, "layer": layer,
            "color": LAYER_COLORS.get(layer, DEFAULT_COLOR)
        })

    def _parse_meta(self, txt):
        for label, key in [("Style Name", "style"), ("Piece Name", "piece"),
                           ("Sample Size", "size"), ("Size", "size")]:
            if txt.startswith(label + ": "):
                v = txt.split(": ", 1)[1].strip()
                if v:
                    self.metadata[key] = v

    def _arc_pts(self, arc, sc, steps=64):
        try:
            cx, cy = arc.dxf.center.x*sc, arc.dxf.center.y*sc
            r = arc.dxf.radius*sc
            sa = math.radians(arc.dxf.start_angle)
            ea = math.radians(arc.dxf.end_angle)
            if ea < sa:
                ea += 2*math.pi
            return [(cx+r*math.cos(sa+(ea-sa)*i/steps),
                     cy+r*math.sin(sa+(ea-sa)*i/steps))
                    for i in range(steps+1)]
        except:
            return []

    def _circle_pts(self, cx, cy, r, steps=72):
        return [(cx+r*math.cos(2*math.pi*i/steps),
                 cy+r*math.sin(2*math.pi*i/steps))
                for i in range(steps+1)]

# Preview Renderer
class PreviewRenderer:
    BG = (13, 15, 20)
    GRID_MAJ = (35, 42, 65)
    GRID_MIN = (20, 26, 44)

    def render(self, parser, cw, ch, zoom=1.0):
        img = Image.new("RGB", (cw, ch), self.BG)
        draw = ImageDraw.Draw(img)
        if not parser.entities or not parser.bounds:
            draw.text((cw//2-100, ch//2), "DXF ফাইল আপলোড করুন", fill=(120, 140, 180))
            return img
        b = parser.bounds
        dw = (b[2]-b[0]) or 1
        dh = (b[3]-b[1]) or 1
        RULER = 38
        aw = cw-RULER
        ah = ch-RULER
        base = min(aw/dw, ah/dh) * 0.88
        scale = base * zoom
        cx = RULER + aw/2
        cy = RULER + ah/2
        mxc = (b[0]+b[2])/2
        myc = (b[1]+b[3])/2
        def tx(x): return cx + (x-mxc)*scale
        def ty(y): return cy - (y-myc)*scale
        # Draw graded polys
        if parser.graded_polys and parser.rul_parser:
            sizes = parser.rul_parser.sizes
            sample = parser.rul_parser.sample
            for si, sname in enumerate(sizes):
                if sname == sample:
                    continue
                polys = parser.graded_polys.get(sname, [])
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                for poly_pts in polys:
                    if len(poly_pts) < 2:
                        continue
                    sc2 = [(int(tx(p[0])), int(ty(p[1]))) for p in poly_pts]
                    for i in range(len(sc2)-1):
                        x1, y1 = sc2[i]
                        x2, y2 = sc2[i+1]
                        if RULER <= x1 <= cw and RULER <= y1 <= ch and \
                           RULER <= x2 <= cw and RULER <= y2 <= ch:
                            draw.line([(x1, y1), (x2, y2)], fill=col, width=1)
        # Draw base entities
        for ent in parser.entities:
            pts = ent["points"]
            lay = ent.get("layer", "1")
            col = ent.get("color", DEFAULT_COLOR)
            if len(pts) < 2:
                continue
            lw = 2 if lay == "1" else 1
            sc2 = [(int(tx(p[0])), int(ty(p[1]))) for p in pts]
            for i in range(len(sc2)-1):
                x1, y1 = sc2[i]
                x2, y2 = sc2[i+1]
                if RULER <= x1 <= cw and RULER <= y1 <= ch and \
                   RULER <= x2 <= cw and RULER <= y2 <= ch:
                    draw.line([(x1, y1), (x2, y2)], fill=col, width=lw)
        w_cm = round(dw, 1)
        h_cm = round(dh, 1)
        n_sz = len(parser.graded_polys) if parser.graded_polys else 1
        draw.text((RULER+6, 10),
                  f"  {w_cm}x{h_cm}cm  zoom{zoom:.1f}x  sizes:{n_sz}",
                  fill=(110, 140, 200))
        return img

# Exporters
class PDFExporter:
    MARGIN = 1.5
    def export(self, parser, out_path):
        if not parser.bounds:
            raise RuntimeError("No geometry")
        b = parser.bounds
        pad = self.MARGIN
        ox = -b[0]+pad
        oy = -b[1]+pad
        pw = (b[2]-b[0]+2*pad)*cm
        ph = (b[3]-b[1]+2*pad)*cm
        c = pdf_canvas.Canvas(out_path, pagesize=(pw, ph))
        c.setTitle("DXF Pattern")
        def px(x): return (x+ox)*cm
        def py(y): return (y+oy)*cm
        # Draw graded sizes
        if parser.graded_polys and parser.rul_parser:
            sizes = parser.rul_parser.sizes
            for si, sname in enumerate(sizes):
                polys = parser.graded_polys.get(sname, [])
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                c.setLineWidth(0.5 if sname == parser.rul_parser.sample else 0.25)
                c.setStrokeColorRGB(col[0]/255, col[1]/255, col[2]/255)
                for poly_pts in polys:
                    if len(poly_pts) < 2:
                        continue
                    p = c.beginPath()
                    p.moveTo(px(poly_pts[0][0]), py(poly_pts[0][1]))
                    for pt in poly_pts[1:]:
                        p.lineTo(px(pt[0]), py(pt[1]))
                    c.drawPath(p, stroke=1, fill=0)
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

class AIExporter:
    def export(self, parser, out_path):
        # For now, create PDF with AI header
        from reportlab.pdfgen import canvas as pdf_canvas
        from reportlab.lib.units import cm
        if not parser.bounds:
            raise RuntimeError("No geometry")
        b = parser.bounds
        pad = 1.5
        ox = -b[0]+pad
        oy = -b[1]+pad
        pw = (b[2]-b[0]+2*pad)*cm
        ph = (b[3]-b[1]+2*pad)*cm
        tmp_path = out_path.replace(".ai", "_tmp.pdf")
        c = pdf_canvas.Canvas(tmp_path, pagesize=(pw, ph))
        c.setTitle("DXF Pattern")
        def px(x): return (x+ox)*cm
        def py(y): return (y+oy)*cm
        if parser.graded_polys and parser.rul_parser:
            sizes = parser.rul_parser.sizes
            for si, sname in enumerate(sizes):
                polys = parser.graded_polys.get(sname, [])
                col = GRADE_COLORS[si % len(GRADE_COLORS)]
                c.setLineWidth(0.5)
                c.setStrokeColorRGB(col[0]/255, col[1]/255, col[2]/255)
                for poly_pts in polys:
                    if len(poly_pts) < 2:
                        continue
                    p = c.beginPath()
                    p.moveTo(px(poly_pts[0][0]), py(poly_pts[0][1]))
                    for pt in poly_pts[1:]:
                        p.lineTo(px(pt[0]), py(pt[1]))
                    c.drawPath(p, stroke=1, fill=0)
        for ent in parser.entities:
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
        # Add AI header
        with open(tmp_path, "rb") as f:
            pdf_data = f.read()
        ai_prefix = (b"%!PS-Adobe-3.0\n"
                     b"%%Creator: Adobe Illustrator 26.0\n"
                     b"%%Title: Pattern\n%%EndComments\n")
        with open(out_path, "wb") as f:
            f.write(ai_prefix)
            f.write(pdf_data)
        os.remove(tmp_path)

class SVGExporter:
    PAD = 15.0
    def export(self, parser, out_path):
        if not parser.bounds:
            raise RuntimeError("No geometry")
        GRADE_COLORS_HEX = ["#FF5050", "#FFA528", "#C8C800", "#000000",
                           "#28B428", "#1E90FF", "#A028FF"]
        all_pts = []
        if parser.graded_polys and parser.rul_parser:
            for polys in parser.graded_polys.values():
                for poly in polys:
                    for p in poly:
                        all_pts.append((p[0]*10, p[1]*10))
        else:
            for e in parser.entities:
                for p in e["points"]:
                    all_pts.append((p[0]*10, p[1]*10))
        if not all_pts:
            raise RuntimeError("No geometry")
        xs = [p[0] for p in all_pts]
        ys = [p[1] for p in all_pts]
        b = (min(xs), min(ys), max(xs), max(ys))
        pad = self.PAD
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
            f'  <!-- DXF Pattern -->',
            ''
        ]
        if parser.graded_polys and parser.rul_parser:
            sizes = parser.rul_parser.sizes
            for si, sname in enumerate(sizes):
                polys = parser.graded_polys.get(sname, [])
                col = GRADE_COLORS_HEX[si % len(GRADE_COLORS_HEX)]
                sw = "0.5" if sname == parser.rul_parser.sample else "0.3"
                lines.append(f'  <g id="Size_{sname}">')
                for poly in polys:
                    if len(poly) < 2:
                        continue
                    d = f"M {sx(poly[0][0]*10)},{sy(poly[0][1]*10)}"
                    for pt in poly[1:]:
                        d += f" L {sx(pt[0]*10)},{sy(pt[1]*10)}"
                    lines.append(f'    <path d="{d}" fill="none" stroke="{col}" stroke-width="{sw}"/>')
                lines.append(f'  </g>')
        else:
            lines.append('  <g id="Base">')
            for ent in parser.entities:
                pts = ent["points"]
                if len(pts) < 2:
                    continue
                d = f"M {sx(pts[0][0]*10)},{sy(pts[0][1]*10)}"
                for pt in pts[1:]:
                    d += f" L {sx(pt[0]*10)},{sy(pt[1]*10)}"
                lines.append(f'    <path d="{d}" fill="none" stroke="#000" stroke-width="0.5"/>')
            lines.append('  </g>')
        lines.append('</svg>')
        with open(out_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))

class DXFSaver:
    def save(self, parser, out_path):
        doc = ezdxf.new("R2010")
        doc.header["$INSUNITS"] = 4
        msp = doc.modelspace()
        def tmm(v):
            return v*10.0
        for ent in parser.entities:
            etype = ent["type"]
            pts = ent["points"]
            lay = ent.get("layer", "1")
            if len(pts) < 2:
                continue
            mm_pts = [(tmm(p[0]), tmm(p[1])) for p in pts]
            msp.add_lwpolyline(mm_pts, dxfattribs={"layer": lay})
        doc.saveas(out_path)

# API Routes
@app.route('/api/upload', methods=['POST'])
def upload():
    try:
        if 'file' not in request.files:
            return jsonify({'success': False, 'error': 'No file found'}), 400
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
        n_grades = len(parser.graded_polys) if parser.graded_polys else 0
        return jsonify({
            'success': True,
            'preview': preview_b64,
            'info': f"Entities: {len(parser.entities)}\nWidth: {w} cm\nHeight: {h} cm\nGrading: {n_grades} sizes",
            'has_grading': n_grades > 0
        })
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/api/upload_rul', methods=['POST'])
def upload_rul():
    try:
        session_id = request.remote_addr
        if session_id not in active_parser:
            return jsonify({'success': False, 'error': 'Upload DXF first'}), 400
        if 'file' not in request.files:
            return jsonify({'success': False, 'error': 'No file found'}), 400
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
            'sample': rul.sample,
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
        elif format_type == 'ai':
            AIExporter().export(parser, output_path)
        elif format_type == 'svg':
            SVGExporter().export(parser, output_path)
        elif format_type == 'dxf':
            DXFSaver().save(parser, output_path)
        else:
            return jsonify({'success': False, 'error': 'Format not supported'}), 400
        return send_file(output_path, as_attachment=True, download_name=output_filename)
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

@app.route('/')
def index():
    return jsonify({'status': 'API is running', 'version': VERSION})

@atexit.register
def cleanup():
    try:
        shutil.rmtree(UPLOAD_FOLDER)
        shutil.rmtree(OUTPUT_FOLDER)
    except:
        pass

if __name__ == '__main__':
    app.run(debug=True, host='0.0.0.0', port=5000)
