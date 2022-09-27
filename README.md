# domainbinder


```shell
pip freeze > requirements.txt
```

```shell
python3 -m venv .venv
pip install -r requirements.txt
sudo apt install chromium-driver
```

```shell
$ source .venv/bin/activate
$ cat > config.py
secret_key = "xwb6QU7TefPvZz2rUx4rOjyzHItMQDkE"
secret_id = "xKIDylJabSs8IBnNXRR8p58vRX5OUQ3rpzJ"
router_login_passwd = "welcome@pi.ldd.cool:)"
router_ip_file = "/home/ldd/domainbinder/router-ip"
log_file = "/home/ldd/domainbinder/app.log"

$ ./domainbinder
```

```shell
python router_public_ip.py
```
