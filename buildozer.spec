[app]

title = Asia Mail Client Pro
package.name = asiamail
package.domain = com.hima

source.dir = .
source.include_exts = py,png,jpg,kv,wav

version = 1.0

requirements = python3,kivy,kivymd,beautifulsoup4,dnspython,certifi

orientation = portrait

fullscreen = 0

android.api = 34
android.minapi = 24
android.sdk = 34
android.ndk = 25b
android.accept_sdk_license = True

[buildozer]

log_level = 2
warn_on_root = 1
