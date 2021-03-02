import requests

url = 'https://quotes.rest/qod'
response = requests.get(url)

if response.ok:
    data = response.json()
    # print(data)
    quote = data['contents']['quotes'][0]['quote']
    print(quote)
else:
    print('Neuspesan get zahtev')
