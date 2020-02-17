from PIL import Image
from PIL import ImageFont
from PIL import ImageDraw

font = ImageFont.truetype("TerminusTTF-Bold-4.46.0.ttf", 20)
def write(face, msg, name):
    img = Image.open("template.png")
    draw = ImageDraw.Draw(img)
    #draw.fontmode = "1"
    msg = msg.split('\n')
    # First line at (23, 23)
    draw.text((23, 20), msg[0], (255,255,255), font=font)
    # Second line at (23, 47)
    if len(msg) >= 2:
        draw.text((23, 44), msg[1], (255,255,255), font=font)
    # Even more...?
    if len(msg) >= 3:
        draw.text((23, 68), msg[2], (255,255,255), font=font)
    # Please stop
    if len(msg) >= 4:
        draw.text((23, 92), msg[3], (255,255,255), font=font)
    # Face at (498, 18)
    faceimg = Image.open("OneShot_Faces/"+face+".png")
    img.paste(faceimg, (498, 18))
    img.save(name)

def preprocess():
    file = open("transcript.txt")
    L = []
    while 1:
        line = file.readline()
        if line.startswith("END"): break
        if line[0] != "[": continue
        br = line.find("]")
        face = line[1:br]
        msg = line[br+1:].strip().replace('\\n', '\n')
        L.append((face, msg))
    return L

L = preprocess()
for i, tup in enumerate(L):
    write(*tup, str(i)+".png")
