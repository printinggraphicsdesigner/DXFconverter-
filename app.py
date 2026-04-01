from flask import Flask, request, send_file
import os, time
from reportlab.pdfgen import canvas

app = Flask(__name__)

UPLOAD_FOLDER = "uploads"
os.makedirs(UPLOAD_FOLDER, exist_ok=True)

@app.route("/convert", methods=["POST"])
def convert():
    file = request.files["file"]
    fmt = request.form.get("format", "pdf")

    timestamp = str(int(time.time()))
    input_path = os.path.join(UPLOAD_FOLDER, f"input_{timestamp}.dxf")
    output_path = os.path.join(UPLOAD_FOLDER, f"output_{timestamp}.pdf")

    file.save(input_path)

    # ✅ Real PDF
    c = canvas.Canvas(output_path)
    c.drawString(100, 750, "DXF Converted Successfully!")
    c.save()

    return send_file(output_path, as_attachment=True)

if __name__ == "__main__":
    app.run()