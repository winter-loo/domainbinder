import json
import requests
# pip install js2py
import js2py
from bs4 import BeautifulSoup

password = '20170926@ldd.cool:)'
urls = {
    'login_page': 'http://192.168.2.1/html/index.html#/login',
    'user_login_nonce': 'http://192.168.2.1/api/system/user_login_nonce',
    'user_login_proof': 'http://192.168.2.1/api/system/user_login_proof',
    'wandetect': 'http://192.168.2.1/api/ntwk/wandetect'
}

session = requests.session()
res = session.get(urls['login_page'])
html = BeautifulSoup(res.text, features="html.parser")
csrf_param = html.find('meta', attrs = {'name': 'csrf_param'})['content']
csrf_token = html.find('meta', attrs = {'name': 'csrf_token'})['content']
csrf = {
    "csrf_param": csrf_param,
    "csrf_token": csrf_token
}

cat_enc_js = ""
login_nonce_js = ""
login_proof_js = ""
with open('js/cat_enc.js') as f:
    cat_enc_js = f.read()
with open('js/login_nonce.js') as f:
    login_nonce_js = f.read()
with open('js/login_proof.js') as f:
    login_proof_js = f.read()

encjs = js2py.eval_js(f'{cat_enc_js}\n{login_nonce_js}').to_dict()
data = {
    "data": encjs["data"],
    "csrf": csrf
}

# print(json.dumps(data))
login_nonce_res = session.post(urls['user_login_nonce'], json=data).text
js = f"""
{cat_enc_js}
var scram = CryptoJS.SCRAM({{keySize: 8}});
var password="{password}";
var firstNonce="{data["data"]["firstnonce"]}";
var res={login_nonce_res};
{login_proof_js}
"""
# with open('foo.js', 'w') as f:
#     f.write(js)
param1 = js2py.eval_js(js).to_dict()
# print(param1)

# update csrf and data
jres = json.loads(login_nonce_res)
csrf = {
    "csrf_token": jres["csrf_token"],
    "csrf_param": jres["csrf_param"]
}
data = {
    "data": param1["data"],
    "csrf": csrf
}

session.post(url=urls['user_login_proof'], json=data)
res = session.get(url=urls['wandetect']).text
print(json.loads(res)["ExternalIPAddress"])


