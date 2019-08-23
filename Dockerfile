# name the portage image
FROM gentoo/portage:latest AS portage

# container to download the latest source code
# avoiding to install git in the gentoo container
FROM alpine/git:latest AS source
RUN cd / && git clone https://github.com/gzoumix/pdepa.git

# image is based on stage3-amd64
FROM gentoo/stage3-amd64:latest
LABEL maintainer="Michael Lienhardt"
LABEL email="michael.lienhardt@laposte.net"

# copy the entire portage volume in
COPY --from=portage /var/db/repos/gentoo /var/db/repos/gentoo

# copy the pdepa code
COPY --from=source /pdepa /opt/pdepa

# continue with image build ...
RUN eselect profile set default/linux/amd64/17.1 && \
    emerge -qv dev-python/pip && \
    pip install --user z3-solver lrparsing


