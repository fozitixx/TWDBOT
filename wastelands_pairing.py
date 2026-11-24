"""Per-Windows-user Wastelands pairing, independent of the release directory."""
import ctypes
import json
import os
import re
import tempfile
from pathlib import Path


def _protect(data, decrypt=False):
    if os.name != "nt":
        return data
    from ctypes import wintypes

    class Blob(ctypes.Structure):
        _fields_ = [("size", wintypes.DWORD), ("data", ctypes.c_void_p)]

    buffer = ctypes.create_string_buffer(data)
    source = Blob(len(data), ctypes.addressof(buffer))
    output = Blob()
    api = ctypes.windll.crypt32
    call = api.CryptUnprotectData if decrypt else api.CryptProtectData
    # Current user's DPAPI scope. Pairing never needs an interactive prompt.
    if not call(ctypes.byref(source), None, None, None, None, 1, ctypes.byref(output)):
        raise ctypes.WinError()
    try:
        return ctypes.string_at(output.data, output.size)
    finally:
        ctypes.windll.kernel32.LocalFree(ctypes.c_void_p(output.data))


def valid_key(value):
    return isinstance(value,str) and re.fullmatch(r"[A-Za-z0-9_-]{24,96}",value) is not None


class PairingProfile:
    def __init__(self, directory):
        self.directory = Path(directory)

    def read(self, name):
        try:
            data = (self.directory/name).read_bytes()
        except FileNotFoundError:
            return {}
        obj = json.loads(data if name=="resume.json" else _protect(data, decrypt=True))
        if not isinstance(obj, dict):
            raise ValueError("Повреждена сохранённая привязка Wastelands")
        return obj

    def write(self, name, value, *, create=False):
        data = json.dumps(value, ensure_ascii=False).encode("utf-8")
        if name!="resume.json":
            data = _protect(data)
        self.directory.mkdir(parents=True,exist_ok=True,mode=0o700)
        with tempfile.NamedTemporaryFile(dir=self.directory,delete=False) as tmp:
            path = Path(tmp.name)
            try:
                tmp.write(data)
                tmp.flush()
                os.fsync(tmp.fileno())
                tmp.close()
                if create:
                    try:
                        if os.name == "nt":
                            # Windows rename publishes a complete file and fails if a peer won.
                            os.rename(path, self.directory / name)
                        else:
                            os.link(path, self.directory / name)
                    except FileExistsError:
                        return False
                else:
                    os.replace(path,self.directory/name)
                return True
            finally:
                path.unlink(missing_ok=True)

    def forget(self, name):
        (self.directory/name).unlink(missing_ok=True)

    def host_keys(self, defaults):
        saved = self.read("host.keys")
        if not saved:
            if self.write("host.keys",defaults,create=True):
                return dict(defaults)
            saved = self.read("host.keys")
        keys = {i:saved.get(str(i)) for i in defaults}
        if not all(valid_key(k) for k in keys.values()):
            keys = {i:key if valid_key(key) else defaults[i] for i,key in keys.items()}
            self.write("host.keys",keys)
        return keys

    def peer(self):
        saved = self.read("peer.key")
        if (type(saved.get("player")) is int and saved["player"] in (1,2,3)
                and valid_key(saved.get("key")) and isinstance(saved.get("host"),str)):
            return saved
        return {}
