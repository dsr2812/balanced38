"""Build the libb38 cdylib and bundle it into the Python wheel.

The wheel carries the native library as package data; the ctypes wrapper
in libb38/__init__.py loads it at import time. No compiler needed by the
consumer — only by the builder.
"""

import glob
import os
import shutil
import subprocess
import sys

from setuptools import setup
from setuptools.command.build_py import build_py

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
PKG = os.path.join(os.path.dirname(__file__), "libb38")


def build_shared_lib():
    env = dict(os.environ)
    subprocess.check_call(["cargo", "build", "-p", "libb38"], cwd=ROOT, env=env)
    for pattern in ("liblibb38.so", "liblibb38.dylib", "liblibb38.dll"):
        for src in glob.glob(os.path.join(ROOT, "target", "debug", pattern)):
            dst = os.path.join(PKG, os.path.basename(src))
            shutil.copy2(src, dst)
            print(f"bundled {dst}")


class build_py_with_lib(build_py):
    def run(self):
        build_shared_lib()
        super().run()


if __name__ == "__main__":
    if not os.environ.get("LIBB38_SKIP_BUILD"):
        build_shared_lib()
    setup(cmdclass={"build_py": build_py_with_lib})