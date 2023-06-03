import re
import json

WHITELIST_FILE = "../../WebBackend/settings_whitelist.json"

def epf_to_json(epf_file, overriden_settings_file=None):
    res = []
    allowed_settings = set()
    with open(WHITELIST_FILE) as f:
        for plugin, settings in json.load(f).items():
            for s in settings:
                allowed_settings.add((plugin, s))
    if overriden_settings_file:
        with open(overriden_settings_file) as f:
            overriden_settings = json.load(f)
    else:
        overriden_settings = []
    for s in overriden_settings:
        plugin = s["plugin_id"]
        key = s["key"]
        if (plugin, key) not in allowed_settings:
            continue
        allowed_settings.remove((plugin, key))
        if "default" in s:
            setting = s["default"]
            res.append(build_dict(plugin, s.get("name", key), key,
                                  s.get("visible", False), setting,
                                  get_type_string(setting)))
    with open(epf_file) as f:
        for l in f:
            m = re.match(r'/instance/(.*?)/(.*)=(.*)', l)
            if not m:
                continue
            plugin = m.group(1)
            key = m.group(2).replace("\\", "")
            if (plugin, key) not in allowed_settings:
                continue
            setting, type = get_typed_setting(m.group(3).strip())
            res.append(build_dict(plugin, key, key, False, setting, type))
    return json.dumps(res, indent=2)

    
def build_dict(plugin, name, key, visible, setting, type):
    id = plugin.rpartition(".")[2] + "." + \
         ".".join(key.lower().replace(".", "").split())
    return {"plugin_id": plugin, "name": name, "key": key, "id": id,
            "visible": visible, "default": setting, "type": type}


def get_type_string(obj):
    if isinstance(obj, bool):
        return "bool"
    if isinstance(obj, int):
        return "int"
    if isinstance(obj, float):
        return "real"
    return "string"


def get_typed_setting(setting):
    if setting in ["true", "false"]:
        return setting == "true", "bool"
    if setting.isnumeric():
        return int(setting), "int"
    try:
        return float(setting), "real"
    except ValueError:
        return setting, "string"


if __name__ == "__main__":
    import sys

    if len(sys.argv) == 2:
        print(epf_to_json(sys.argv[1]))
    if len(sys.argv) == 3:
        print(epf_to_json(sys.argv[1], sys.argv[2]))
