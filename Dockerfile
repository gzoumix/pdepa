# name the portage image
FROM gentoo/portage:latest AS portage

# container to download the latest source code
# avoiding to install git in the gentoo container
FROM alpine/git:latest AS source
RUN cd / && git clone https://github.com/gzoumix/pdepa.git

# image is based on stage3-amd64
FROM gentoo/stage3-amd64:latest
MAINTAINER Jacopo Mauro

# copy the entire portage volume in
COPY --from=portage /usr/portage /usr/portage

# copy the pdepa code
COPY --from=source /pdepa /pdepa

# continue with image build ...
RUN emerge -qv dev-python/pip && \
  pip install --user z3-solver lrparsing
