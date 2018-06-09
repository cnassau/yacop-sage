ARG SAGE_VERSION=8.2
FROM cnassau/yacop-base:$SAGE_VERSION

LABEL maintainer="Christian Nassau <nassau@nullhomotopie.de>"

USER sage
ENV HOME /home/sage
WORKDIR /home/sage
ADD --chown=sage . /tmp/yacop
RUN echo "Running docker-install.sh" \
    && cd /tmp/yacop && sage -sh docker-install.sh \
    && echo "Starting Sage once" && echo "quit();" | env SAGE_BANNER=no sage \
    && echo "Cleaning up" \
    && rm -rf /tmp/* \
    && sync 

ENTRYPOINT [ "sage-entrypoint" ]
CMD [ "sage" ]
