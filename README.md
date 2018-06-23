# yacop-sage

Yet Another Cohomology Program

## Docker quickstart

### Basic invocation

```bash
docker run --rm -it cnassau/yacop-sage
```

### Persistent data storage

```bash
docker run -v /path/to/your/directory:/data --rm -it cnassau/yacop-sage
```

### Using the graphical frontend

```bash
xhost local:docker
docker run -e DISPLAY=$DISPLAY -v /tmp/.X11-unix:/tmp/.X11-unix --rm -it cnassau/yacop-sage
```

### Running without startup banner

```bash
xhost local:docker
docker run -e SAGE_BANNER=NO --rm -it cnassau/yacop-sage
```

### Running the Jupyter notebook

```bash
docker run -p8888:8888 cnassau/yacop-sage sage-jupyter
```
