import shutil
import subprocess
from pathlib import Path

rootdir = Path(__file__).parent.resolve()
desops_regal = rootdir.joinpath("DESops", "random_DFA", "regal-1.08.0929")
regaldir = desops_regal.joinpath("regal")


def build(setup_kwargs):
    """
    This function is mandatory in order to build the extensions.
    """

    if regaldir.exists():
        shutil.rmtree(regaldir)

    makeopts = {"cwd": desops_regal, "check": True}
    subprocess.run(["make", "install-user"], **makeopts)
    subprocess.run(["make", "desops"], **makeopts)
