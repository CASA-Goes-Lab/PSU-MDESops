from importlib.metadata import version

from DESops import __version__


def test_version():
    assert __version__ == version("DESops")
