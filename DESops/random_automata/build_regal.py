import platform
import shutil
import subprocess
from pathlib import Path

rootdir = Path(__file__).parent.resolve()
desops_regal = rootdir.joinpath("regal-1.08.0929")
regaldir = desops_regal.joinpath("regal")


def build(setup_kwargs):
    """
    This function is mandatory in order to build the extensions.

    Only works with g++/Linux (or WSL, etc)
    Have to build manually on windows
    """

    if regaldir.exists():
        shutil.rmtree(regaldir)

    makeopts = {"cwd": desops_regal, "check": True}
    output = subprocess.run(["make", "install-user"], **makeopts)

    subprocess.run(["make", "desops"], **makeopts)
    win_exe = desops_regal.joinpath("random_DFA.exe")
    if platform.system() == "Windows" and win_exe.exists():
        win_exe.rename(desops_regal.joinpath("random_DFA"))
