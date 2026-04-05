"""
Flaremo DXF Converter - Flask Web API
Optimized for High-Precision Curves and Corners
"""
VERSION = "v2.1"
from flask import Flask, request, jsonify, send_file
from flask_cors import CORS
import os, io, base64, math, re, tempfile, shutil, atexit
from reportlab.pdfgen import canvas as pdf_canvas
from reportlab.lib.units import cm
import ezdxf
from ezdxf import recover as dxf_recover
from ezdxf import path  # কার্ভের নিখুঁত ক্যালকুলেশনের জন্য
from PIL import Image, ImageDraw

app = Flask(__name__)
CORS(app)
app.config['MAX_CONTENT_LENGTH'] = 50 * 1024 * 1024

UPLOAD_FOLDER = tempfile.mkdtemp()
OUTPUT_FOLDER = tempfile.mkdtemp()
app.config['UPLOAD_FOLDER'] = UPLOAD_FOLDER
app.config['OUTPUT_FOLDER'] = OUTPUT_FOLDER

# COLORS & CONFIG
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

# --- RUL Parser and Math Utilities remain same ---
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
        if m: self.sizes = m.group(1).strip().split()
        m = re.search(r"SAMPLE SIZE:\s*(\S+)", text)
        if m: self.sample = m.group(1).strip()
        if self.sample in self.sizes: self.sample_idx = self.sizes.index(self.sample)
        blocks = re.split(r"RULE:\s*DELTA\s+(\d+)", text)
        i = 1
        while i < len(blocks) - 1:
            rnum = int(blocks[i])
            pairs = re.findall(r"(-?\d+\.?\d*),\s*(-?\d+\.?\d*)", blocks[i+1])
            if pairs: self.rules[rnum] = [(float(x), float(y)) for x, y in pairs]
            i += 2

    def get_delta_mm(self, rule_num, size_idx):
        if rule_num in self.rules and size_idx < len(self.rules[rule_num]):
            return self.rules[rule_num][size_idx]
        return (0.0, 0.0)

def _arc_length(pts, i1, i2):
    total = 0.0
    for k in range(i1, i2):
        total += math.hypot(pts[k+1][0]-pts[k][0], pts[k+1][1]-pts[k][1])
    return total

def compute_graded_poly(base_pts, grade_indices, rul, size_idx):
    # Logic remains same but accuracy improved via high-density points
    n = len(base_pts) - 1
    if not grade_indices: return list(base_pts)
    grade_deltas = {gi: (rul.get_delta_mm(rule, size_idx)[0]*0.1, rul.get_delta_mm(rule, size_idx)[1]*0.1) 
                    for gi, rule in grade_indices}
    graded = []
    for pi in range(len(base_pts)):
        pt = base_pts[pi]
        pi_mod = pi % n
        if pi_mod in grade_deltas:
            dx, dy = grade_deltas[pi_mod]
            graded.append((pt[0] + dx, pt[1] + dy))
        else:
            # Linear interpolation for non-grade points
            prev_gi = max([gi for gi, r in grade_indices if gi <= pi_mod] or [grade_indices[-1][0]])
            next_gi = min([gi for gi, r in grade_indices if gi >= pi_mod] or [grade_indices[0][0]])
            dx_a, dy_a = grade_deltas[prev_gi]
            dx_b, dy_b = grade_deltas[next_gi]
            len_ap = _arc_length(base_pts, prev_gi, pi_mod)
            len_ab = _arc_length(base_pts, prev_gi, next_gi) if next_gi > prev_gi else 1.0
            t = max(0.0, min(1.0, len_ap / len_ab))
            graded.append((pt[0] + dx_a + t*(dx_b-dx_a), pt[1] + dy_a + t*(dy_b-dy_a)))
    return graded

class AAMAParser:
    def __init__(self):
        self.entities = []
        self.bounds = None
        self.scale = 0.1
        self.metadata = {}
        self.grade_indices = []
        self.graded_polys = {}
        self._base_cut_polys = []

    def parse(self, filepath):
        try:
            doc, _ = dxf_recover.readfile(filepath)
            msp = doc.modelspace()
            
            # অটোমেটিক স্কেল ডিটেকশন (MM vs CM)
            extents = msp.get_bounding_box()
            self.scale = 0.1 if (extents[1].x - extents[0].x) > 50 else 1.0

            # পয়েন্ট রুলস কালেকশন (Grading এর জন্য)
            point_rules = {}
            for ent in msp:
                if ent.dxftype() == "TEXT" and str(ent.dxf.layer) == "1":
                    txt = ent.dxf.text.strip()
                    if txt.startswith("#"):
                        key = (round(ent.dxf.insert.x * self.scale, 4), 
                               round(ent.dxf.insert.y * self.scale, 4))
                        point_rules[key] = int(txt[1:])

            # মেইন এনটিটি প্রসেসিং (High Precision Curves)
            for ent in msp:
                t = ent.dxftype()
                lay = str(getattr(ent.dxf, "layer", "1"))
                
                # কার্ভ এবং পলিলাইন প্রসেসিং (ezdxf.path ব্যবহার করে)
                if t in ("LWPOLYLINE", "POLYLINE", "SPLINE", "ARC", "CIRCLE", "LINE"):
                    try:
                        # ezdxf.path.make_path নিখুঁত কার্ভ জেনারেট করে
                        p = path.make_path(ent)
                        # distance=0.005 মানে হলো প্রতি ০.০৫ মিলিমিটারে একটি পয়েন্ট নেওয়া
                        # এটি কার্ভকে লেকট্রার মতো স্মুথ করবে
                        pts = [(pt.x * self.scale, pt.y * self.scale) 
                               for pt in p.flattening(distance=0.005)]
                        
                        if pts:
                            self._add(t, pts, lay)
                            if lay == "1":
                                self._base_cut_polys.append(pts)
                                # গ্রেড পয়েন্ট ম্যাচিং
                                gi = []
                                for vi, pt in enumerate(pts[:-1]):
                                    pk = (round(pt[0], 4), round(pt[1], 4))
                                    if pk in point_rules: gi.append((vi, point_rules[pk]))
                                if gi and not self.grade_indices: self.grade_indices = gi
                    except:
                        continue
                
                elif t in ("TEXT", "MTEXT"):
                    self._parse_text(ent)

            self._update_bounds()
        except Exception as e:
            raise RuntimeError(f"DXF Parse Error: {e}")

    def _parse_text(self, ent):
        try:
            txt = ent.dxf.text if ent.dxftype() == "TEXT" else ent.plain_mtext()
            txt = txt.strip()
            if txt and not txt.startswith("#"):
                self.entities.append({
                    "type": "TEXT", "points": [(ent.dxf.insert.x*self.scale, ent.dxf.insert.y*self.scale)],
                    "text": txt, "layer": str(ent.dxf.layer), "color": DEFAULT_COLOR
                })
        except: pass

    def _add(self, etype, pts, layer):
        # কোঅর্ডিনেট রাউন্ডিং বাড়ানো হয়েছে নিখুঁত কর্নারের জন্য
        pts = [(round(p[0], 6), round(p[1], 6)) for p in pts]
        self.entities.append({
            "type": etype, "points": pts, "layer": layer,
            "color": LAYER_COLORS.get(layer, DEFAULT_COLOR)
        })

    def attach_rul(self, rul):
        self.graded_polys = {}
        if not self._base_cut_polys: return
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

# --- Renderer, Exporters and API remain largely same with precision improvements ---
# (PreviewRenderer, ActualSizePDFExporter, SVGExporter are same as before)

# ... (বাকি এক্সপোর্টার কোড আগের মতোই থাকবে, শুধু AAMAParser আপডেট করলেই সমস্যা মিটে যাবে)

@app.route('/api/upload', methods=['POST'])
def upload():
    try:
        file = request.files['file']
        filepath = os.path.join(app.config['UPLOAD_FOLDER'], file.filename)
        file.save(filepath)
        parser = AAMAParser()
        parser.parse(filepath)
        active_parser[request.remote_addr] = parser
        
        img = PreviewRenderer().render(parser, 1000, 800, 1.0) # উচ্চতর রেজোলিউশন প্রিভিউ
        buffer = io.BytesIO()
        img.save(buffer, format='PNG')
        
        b = parser.bounds
        return jsonify({
            'success': True,
            'preview': base64.b64encode(buffer.getvalue()).decode(),
            'info': f"Width: {round(b[2]-b[0],2)} cm\nHeight: {round(b[3]-b[1],2)} cm",
            'has_grading': len(parser.grade_indices) > 0
        })
    except Exception as e:
        return jsonify({'success': False, 'error': str(e)}), 500

# (বাকি API এন্ডপয়েন্টগুলো আগের কোড থেকেই কপি করে নিন)

if __name__ == '__main__':
    app.run(debug=True, host='0.0.0.0', port=5000)
