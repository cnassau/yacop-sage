#!/bin/sh

set -e

echo "Installing Yacop Tcl package"
mkdir $SAGE_LOCAL/lib/yacoptcl || true 
cp -rf tcl/* $SAGE_LOCAL/lib/yacoptcl 

echo "Installing Yacop Python package"
sage --python ./setup.py install

cat >> ~/.sage/init.sage <<EOF
from yacop import *
import yacop.utils.startup
yacop.utils.startup.__print_banner__()
EOF

echo "Done"

