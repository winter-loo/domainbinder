var scram = CryptoJS.SCRAM({ keySize: 8 });
var firstNonce = scram.nonce().toString();
var param = { name: 'user_login_nonce', data: { username: 'admin', firstnonce: firstNonce } };