import json
import sys

def najtopliji(gradovi, min_temp, max_vlaznost):
    return list(filter(lambda grad: grad["temp"] >= min_temp and grad["vlaznost"] <= max_vlaznost, gradovi))

if __name__=='__main__':

    if len(sys.argv) != 2:
        print("Nevalidan broj argumenata")
        exit()

    filename = sys.argv[1]

    min_temp = float(input())
    max_vlaznost = float(input())

    with open(filename) as f:
        gradovi = json.load(f)

    najtopliji_gradovi = najtopliji(gradovi, min_temp, max_vlaznost)
    najtopliji_sortirano = sorted(najtopliji_gradovi, key=lambda grad: (grad["temp"], grad["vlaznost"]), reverse=True)
    for grad in najtopliji_sortirano:
        print(grad["grad"], grad["temp"], grad["vlaznost"])
