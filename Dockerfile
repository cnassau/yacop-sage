ARG SAGE_VERSION=8.2
FROM cnassau/yacop-base:$SAGE_VERSION

LABEL maintainer="Christian Nassau <nassau@nullhomotopie.de>"

USER root
RUN mkdir /data && chown sage:sage /data
VOLUME /data/

USER sage
ENV HOME=/home/sage
ENV SAGE_TIMEOUT=3600 SAGE_TIMEOUT_LONG=3600
ENV YACOP_DOUBLECHECK=1
WORKDIR /home/sage
ADD --chown=sage . /tmp/yacop
RUN echo "Running docker-install.sh" \
    && cd /tmp/yacop && sage -sh docker-install.sh \
    && echo "Starting Sage once" && echo "quit();" | env SAGE_BANNER=no sage \
    && echo "Cleaning up" \
    && rm -rf /tmp/* \
    && cd /home/sage && ln -s /data yacop_data \
    && sync 

ENTRYPOINT [ "sage-entrypoint" ]
CMD [ "sage" ]

