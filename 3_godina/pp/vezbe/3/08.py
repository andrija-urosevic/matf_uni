import json
import sys

if len(sys.argv) != 2:
    exit('Args error')

with open('tacke.json') as f:
    tacke = json.load(f)

def kvadrant(tacka):
    if tacka['koordinate'][0] > 0 and tacka['koordinate'][1] > 0 and int(sys.argv[1]) == 1:
        return True
    if tacka['koordinate'][0] < 0 and tacka['koordinate'][1] > 0 and int(sys.argv[1]) == 2:
        return True
    if tacka['koordinate'][0] < 0 and tacka['koordinate'][1] < 0 and int(sys.argv[1]) == 3:
        return True
    if tacka['koordinate'][0] > 0 and tacka['koordinate'][1] < 0 and int(sys.argv[1]) == 4:
        return True

tacke_kvadranta = list(filter(kvadrant, tacke))
min_tacka = max(tacke_kvadranta, key=lambda x: x['koordinate'][0]**2 + x['koordinate'][1]**2)
print(min_tacka['teme'])
