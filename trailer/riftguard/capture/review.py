import os, sys
from PIL import Image, ImageDraw
names = sys.argv[2:]; out = sys.argv[1]
W, H = 400, 225
sheet = Image.new('RGB', (W*3, H*len(names)))
for r, n in enumerate(names):
    fs = sorted(os.listdir('shots/'+n))
    for c, f in enumerate([fs[0], fs[len(fs)//2], fs[-1]]):
        im = Image.open(f'shots/{n}/{f}').resize((W, H)); d = ImageDraw.Draw(im)
        d.rectangle([0,0,70,16], fill=(0,0,0)); d.text((4,3), f'{n} {f[1:6]}', fill=(255,230,0))
        sheet.paste(im, (c*W, r*H))
sheet.save(out, quality=82)
