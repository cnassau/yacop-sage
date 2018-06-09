#/bin/bash

SAGE_VERSION=8.2
DOCKERID=cnassau

docker build --tag $DOCKERID/yacop-sage:latest --tag $DOCKERID/yacop-sage:$SAGE_VERSION --build-arg SAGE_VERSION=$SAGE_VERSION .
