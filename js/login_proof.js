var salt = CryptoJS.enc.Hex.parse(res['salt']);
var iter = res['iterations'];
var finalNonce = res['servernonce'];
var authMsg = firstNonce + "," + finalNonce + "," + finalNonce;
var saltPassword = scram.saltedPassword(password, salt, iter).toString();
var serverKey = scram.serverKey(CryptoJS.enc.Hex.parse(saltPassword));
var clientKey = scram.clientKey(CryptoJS.enc.Hex.parse(saltPassword)).toString();
var storekey = scram.storedKey(CryptoJS.enc.Hex.parse(clientKey));
storekey = storekey.toString();
var clientsignature = scram.signature(CryptoJS.enc.Hex.parse(storekey), authMsg);
clientsignature = clientsignature.toString();
clientsignature = CryptoJS.enc.Hex.parse(clientsignature);
clientKey = CryptoJS.enc.Hex.parse(clientKey);
for (var i = 0; i < clientKey.sigBytes / 4; i++) {
    clientKey.words[i] = clientKey.words[i] ^ clientsignature.words[i]
}
var param1 = { name: 'user_login_proof', data: { clientproof: clientKey.toString(), finalnonce: finalNonce } };
