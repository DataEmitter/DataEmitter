# Value-Set Analyse
## run the vsa
./run_vsa.sh libgstflxdec.so
## run the activate
set Activated = True and Check_Stitch = False in  /config/gstreamer_config.py
./run_activate.sh libgstflxdec.so
## run stitch
set Activated = False and Check_Stitch = True in  /config/gstreamer_config.py
python3 main.py
