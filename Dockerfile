# Dockerfile for binder
# Reference: https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile

# Temporary work around: the first 8.2 image that was pushed to dockerhub was incompatible
FROM sagemath/sagemath:latest

# Copy the contents of the repo in ${HOME}
COPY --chown=sage:sage . ${HOME}

# Adding git to the list of commands
USER root
RUN apt-get -qq update \
 && apt-get -qq install -y --no-install-recommends git apt-transport-https ca-certificates \
 && apt-get -qq clean
USER sage

# Installing the package and dependencies
RUN sage -pip install .
