"""
Flaremo DXF Converter - Flask Web API
For deployment on Render
"""
VERSION = "v2.0"
from flask import Flask, request, jsonify, send_file
from flask_cors import CORS
import os
import io
import base64
import math
import re
import tempfile
import shutil
from reportlab.pdfgen import canvas as pdf_canvas
from reportlab.lib.units import cm
import ezdxf
from ezdxf import recover as dxf_recover
from PIL import Image, ImageDraw

app = Flask(__name__)
CORS(app)  # Enable CORS for cross-origin requests
app.config['MAX_CONTENT_LENGTH'] = 50 * 1024 * 1024  # 50MB max upload

UPLOAD_FOLDER = tempfile.mkdtemp()
OUTPUT_FOLDER = tempfile.mkdtemp()
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['OUTPUT_FOLDER'] = OUTPUT_FOLDER

# Colors
LAYER_COLORS = {
    "1": (255, 255, 255),
    "14": (100, 220, 100),
    "8": (255, 200, 60),
    "4": (255, 120, 120),
    "7": (50, 50, 80),
}
DEFAULT_COLOR = (79, 142, 247)

# Session storage
active_parser = {}

# RUL Parser
class RULParser:
    def __init__(self):
        self.sizes = []
        self.sample = "M"
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

# DXF Parser
class AAMAParser:
    def __init__(self):
        self.entities = []
        self.bounds = None
        self.scale = 0.1
        self.metadata = {}

    def parse(self, filepath):
        self.entities = []
        self.metadata = {}

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

        for ent in block:
            t = ent.dxftype()
            lay = str(getattr(ent.dxf, "layer", "1"))

            if t == "POLYLINE":
                verts = list(ent.vertices)
                pts = [(v.dxf.location.x*sc, v.dxf.location.y*sc) for v in verts]
                if pts:
                    self._add("POLYLINE", pts, lay)

            elif t == "LWPOLYLINE":
                pts = [(p[0]*sc, p[1]*sc) for p in ent.get_points()]
                if pts:
                    self._add("LWPOLYLINE", pts, lay)

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
                    if txt:
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

    def _update_bounds(self):
        xs, ys = [], []
        for e in self.entities:
            for p in e["points"]:
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
        for label, key in [("Style Name", "style"), ("Piece Name", "piece")]:
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

        def tx(x):
            return cx + (x-mxc)*scale
        def ty(y):
            return cy - (y-myc)*scale

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
        draw.text((RULER+6, 10),
                  f"  {w_cm}x{h_cm}cm  zoom{zoom:.1f}x",
                  fill=(110, 140, 200))

        return img

# PDF Exporter
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

        def px(x):
            return (x+ox)*cm
        def py(y):
            return (y+oy)*cm

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

# DXF Saver
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
            if etype == "TEXT":
                if pts:
                    msp.add_text(ent.get("text", " "), dxfattribs={
                        "insert": (tmm(pts[0][0]), tmm(pts[0][1]), 0),
                        "height": tmm(ent.get("height", 0.25)), "layer": lay
                    })
                continue
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
        
        return jsonify({
            'success': True,
            'preview': preview_b64,
            'info': f"Entities: {len(parser.entities)}\nWidth: {w} cm\nHeight: {h} cm"
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
    app.run(debug=True, port=5000)
