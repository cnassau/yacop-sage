#!/bin/sh

set -e

echo "Installing Yacop Tcl package"
TCLLIB=$SAGE_LOCAL/tcl/lib
sudo mkdir $TCLLIB/yacoptcl || true 
sudo cp -rf tcl/* $TCLLIB/yacoptcl 

echo "Installing Yacop Python package"
cp -ar yacop src
sage --python ./setup.py install

cat >> ~/.sage/init.sage <<EOF
from yacop import *
import yacop.utils.startup
yacop.utils.startup.__print_banner__()
EOF

echo "Done"

