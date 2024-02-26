import sys

case = "gstreamer"

if case == "gstreamer":
    from config.gstreamer_config import *
else:
    sys.exit(-1)
