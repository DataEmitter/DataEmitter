## Primitive Identification
```
python3 ./evalmain.py ../samples/binary/libgstflxdec.so ../samples/dump/gstreamer.dump
```
## Primitive Activation
```
python3 ./ActivateG1.py ./MidResult/libgstflxdec.so/act_config.json
```
## stitch path test
```
python3 ./path_stitch.py ./MidResult/libgstflxdec.so/act_config.json
```