#
# Get public Internet IP from router of 华为路由TC7102
#
# For this script to run on ubuntu raspberry pi, install some prerequisites:
#
#   sudo apt install xvfb
#   pip install pyvirtualdisplay
#   pip install selenium
#
from selenium.webdriver import Chrome
from selenium.webdriver.common.by import By
from selenium.webdriver.common.keys import Keys
from selenium.webdriver.chrome.options import Options
import time
from pyvirtualdisplay import Display
import config

display = Display(visible=0, size=(800, 600))
display.start()

urls = {
    'login_page': 'http://192.168.2.1/html/index.html#/login',
    'user_login_nonce': 'http://192.168.2.1/api/system/user_login_nonce',
    'user_login_proof': 'http://192.168.2.1/api/system/user_login_proof',
    'wandetect': 'http://192.168.2.1/api/ntwk/wandetect'
}

options = Options()
options.add_argument("--headless")
options.add_argument("--disable-gpu")

web = Chrome(options=options)

web.get(urls['login_page'])

time.sleep(1)

web.find_element(By.ID, 'userpassword_ctrl').send_keys(config.router_login_passwd, Keys.ENTER)

time.sleep(1)

# wan ip
el = web.find_element(By.XPATH, '//*[@id="index"]/div[3]/div/div[3]/div/div[3]/p[2]')
print(el.text)

web.quit()
