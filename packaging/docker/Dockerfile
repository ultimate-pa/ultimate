#------------------------------------------------------------------------------
# Dockerfile: compile and package Ultimate products
#------------------------------------------------------------------------------
# Author: Manuel Bentele
# Copyright (c) 2023
#------------------------------------------------------------------------------
# common build arguments for multi-staged Docker build
#------------------------------------------------------------------------------
ARG REPO_DIR_FRONTEND="trunk/source/WebsiteStatic"
ARG REPO_DIR_BUILD="releaseScripts/default"
ARG REPO_DIR_TOOLS="releaseScripts/default/adds"
ARG DIR_BUILD="/home/build"
ARG DIR_ULTIMATE="${DIR_BUILD}/ultimate"
ARG DIR_OUTPUT_BUILD="${DIR_ULTIMATE}/${REPO_DIR_BUILD}"
ARG DIR_OUTPUT_FRONTEND="${DIR_ULTIMATE}/${REPO_DIR_FRONTEND}"
ARG DIR_TOOLS="${DIR_ULTIMATE}/${REPO_DIR_TOOLS}"
ARG USER_NAME="ultimate"
ARG USER_GROUP="ultimate"
ARG USER_HOME="/home/${USER_NAME}"

#------------------------------------------------------------------------------
# 1st build stage: compile and build Ultimate products
#------------------------------------------------------------------------------
FROM alpine:3 AS build-products

ARG REPO_URL="https://github.com/ultimate-pa/ultimate.git"
ARG REPO_BRANCH="dev"

ARG ULTIMATE_MEMORY_HEAP_MAX="12G"
ARG ULTIMATE_MEMORY_STACK_MAX="512M"

ARG REPO_DIR_BUILD
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD

# install build dependencies for an entire Ultimate build
RUN apk add --no-cache "bash" \
                       "git" \
                       "maven" \
                       "openjdk21"

# clone fresh Ultimate Git repository
RUN mkdir -p "${DIR_BUILD}" && \
    git clone --depth=1 --branch="${REPO_BRANCH}" "${REPO_URL}" "${DIR_ULTIMATE}"

# build all Ultimate products
WORKDIR "${DIR_ULTIMATE}"
RUN cd "${DIR_OUTPUT_BUILD}" && bash makeBuild.sh -m "${ULTIMATE_MEMORY_HEAP_MAX}" -s "${ULTIMATE_MEMORY_STACK_MAX}" -p linux

#------------------------------------------------------------------------------
# 2nd build stage: compile and build the Ultimate web interface
#------------------------------------------------------------------------------
FROM build-products AS build-webfrontend

ARG ULTIMATE_FRONTEND_BASEURL="/website"

ARG REPO_DIR_FRONTEND
ARG REPO_DIR_BUILD
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD

# install build dependencies for building the Ultimate web frontend
RUN apk add --no-cache "gcc" \
                       "g++" \
                       "make" \
                       "libc-dev" \
                       "libc++-dev" \
                       "linux-headers" \
                       "python3" \
                       "ruby-full" \
                       "ruby-dev"

# build the Ultimate web frontend
WORKDIR "${REPO_DIR_FRONTEND}"
ENV PATH="${DIR_OUTPUT_BUILD}/UCLI-E4-linux:${PATH}"
RUN python3 scripts/build.py --baseurl "${ULTIMATE_FRONTEND_BASEURL}"

#------------------------------------------------------------------------------
# 2nd build stage: package common Ultimate artifacts shared by all products
#------------------------------------------------------------------------------
FROM alpine:3 AS ultimate-common

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install runtime dependencies for all Ultimate products
RUN apk add --no-cache "libc6-compat" \
                       "openjdk21-jre-headless"

# add the non-root user 'ultimate' for the Ultimate products and prepare
# installation directory for an Ultimate product
RUN mkdir -p "${USER_HOME}" && \
    addgroup "${USER_GROUP}" && \
    adduser -G "${USER_GROUP}" -H -h "${USER_HOME}" -D "${USER_NAME}" && \
    chown -R "${USER_NAME}:${USER_GROUP}" "${USER_HOME}"
WORKDIR "${USER_HOME}"

# make Ultimate executable, scripts, and solvers available
RUN echo "export PATH=\"${USER_HOME}:${PATH}\"" > /etc/profile.d/ultimate_path.sh

# enable colorized prompt
RUN ln -s /etc/profile.d/color_prompt.sh.disabled /etc/profile.d/color_prompt.sh

# add Welcome script to print Ultimate version
ADD "welcome.sh" "/etc/profile.d/welcome.sh"

#------------------------------------------------------------------------------
# 2nd build stage: package Ultimate web frontend
#------------------------------------------------------------------------------
FROM alpine:3 AS ultimate-webfrontend

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_FRONTEND
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

ENV ULTIMATE_FRONTEND_DEBUG="false"
ENV ULTIMATE_FRONTEND_MSG_ORIENTATION="left"

ENV ULTIMATE_FRONTEND_PROTOCOL="http"
ENV ULTIMATE_FRONTEND_HOST="localhost"
ENV ULTIMATE_FRONTEND_PORT="80"
ENV ULTIMATE_FRONTEND_ROUTE="/website"

ENV ULTIMATE_BACKEND_PROTOCOL="http"
ENV ULTIMATE_BACKEND_HOST="localhost"
ENV ULTIMATE_BACKEND_PORT=8080
ENV ULTIMATE_BACKEND_ROUTE="/api"

# install runtime dependencies for the Ultimate web frontend
RUN apk add --no-cache "gcc" \
                       "g++" \
                       "make" \
                       "libc-dev" \
                       "libc++-dev" \
                       "linux-headers" \
                       "ruby-full" \
                       "ruby-dev"

# install 'dockerize' for automatic configuration file creation
ENV DOCKERIZE_VERSION="v0.9.5"
RUN apk add --no-cache "wget" \
                       "openssl" \
                       "curl" && \
    wget -q -O - "https://github.com/jwilder/dockerize/releases/download/${DOCKERIZE_VERSION}/dockerize-alpine-linux-amd64-${DOCKERIZE_VERSION}.tar.gz" | tar xzf - -C "/usr/local/bin" && \
    apk del --no-cache "wget"

# add the non-root user 'ultimate' for the Ultimate web frontend and prepare
# installation directory
RUN mkdir -p "${USER_HOME}" && \
    addgroup "${USER_GROUP}" && \
    adduser -G "${USER_GROUP}" -H -h "${USER_HOME}" -D "${USER_NAME}" && \
    chown -R "${USER_NAME}:${USER_GROUP}" "${USER_HOME}"
WORKDIR "${USER_HOME}"

# install already built Ultimate web frontend
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-webfrontend "${DIR_OUTPUT_FRONTEND}" "${USER_HOME}"
ADD "config.js.tpl" "${USER_HOME}/config.js.tpl"

# install Jekyll to serve the Ultimate web frontend
RUN bundle install

# run the Ultimate web frontend as non-root user
USER "${USER_NAME}"

# define health check to supervise the Ultimate web frontend's availability
HEALTHCHECK --interval=1m --timeout=10s --start-period=20s \
    CMD curl -f "${ULTIMATE_FRONTEND_PROTOCOL}://${ULTIMATE_FRONTEND_HOST}:${ULTIMATE_FRONTEND_PORT}${ULTIMATE_FRONTEND_ROUTE}/" || exit 1

# default entry point to serve the Ultimate web frontend
ENTRYPOINT dockerize -template "config.js.tpl:js/webinterface/config.js" \
                     bundle exec jekyll serve --host "${ULTIMATE_FRONTEND_HOST}" \
                                              --port "${ULTIMATE_FRONTEND_PORT}"

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate CLI
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-cli

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate CLI product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UCLI-E4-linux" "${USER_HOME}"

# run the Ultimate CLI product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate Debug UI
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-debug

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install graphical dependencies for Ultimate Debug UI product
RUN apk add --no-cache "openjdk21-jre" \
                       "libcanberra-gtk3" \
                       "dbus-x11" \
                       "ttf-freefont" \
                       "xauth"

# install already built Ultimate Debug UI product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UDebug-E4-linux" "${USER_HOME}"

# run the Ultimate Debug UI product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate Automizer
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-automizer

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate Automizer product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UAutomizer-linux" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "${USER_HOME}/Automizer"

# run the Ultimate Automizer product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate DeltaDebugger
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-deltadebugger

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate DeltaDebugger product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UDeltaDebugger-linux" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "${USER_HOME}/DeltaDebugger"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate Eliminator
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-eliminator

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate Eliminator product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UEliminator-linux" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "${USER_HOME}/Eliminator"

# run the Ultimate Eliminator product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate GemCutter
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-gemcutter

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate GemCutter product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UGemCutter-linux" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "${USER_HOME}/GemCutter"

# run the Ultimate GemCutter product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate Kojak
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-kojak

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate Kojak product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UKojak-linux" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "${USER_HOME}/Kojak"

# run the Ultimate Kojak product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate Referee
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-referee

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate Referee product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UReferee-linux" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "${USER_HOME}/Referee"

# run the Ultimate Referee product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate ReqAnalyzer
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-reqanalyzer

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate ReqAnalyzer product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UReqCheck-linux" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "${USER_HOME}/ReqAnalyzer"

# run the Ultimate ReqAnalyzer product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate Taipan
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-taipan

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate Taipan product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UTaipan-linux" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "${USER_HOME}/Taipan"

# run the Ultimate Taipan product as non-root user
USER "${USER_NAME}"

# default entry point to print installed Ultimate version
ENTRYPOINT ["/bin/sh", "-l"]

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate WebBackend
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-webbackend

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT_BUILD
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

ARG REPO_DIR_WEBSITE_CONFIG="releaseScripts/website-config"
ARG DIR_WEBSITE_CONFIG="${DIR_ULTIMATE}/${REPO_DIR_WEBSITE_CONFIG}"

ARG ULTIMATE_DIR_TMP="/tmp/ultimate"

ENV ULTIMATE_BACKEND_HOST="localhost"
ENV ULTIMATE_BACKEND_PORT=8080
ENV ULTIMATE_BACKEND_ROUTE="/api"

ENV ULTIMATE_LOG_PATH="/dev/stdout"
ENV ULTIMATE_LOG_LEVEL="INFO"
ENV ULTIMATE_TIMEOUT=90

# create directory to store temporary files
RUN mkdir -p "${ULTIMATE_DIR_TMP}"

# install 'dockerize' for automatic configuration file creation
ENV DOCKERIZE_VERSION="v0.9.5"
RUN apk add --no-cache "wget" \
                       "openssl" \
                       "curl" && \
    wget -q -O - "https://github.com/jwilder/dockerize/releases/download/${DOCKERIZE_VERSION}/dockerize-alpine-linux-amd64-${DOCKERIZE_VERSION}.tar.gz" | tar xzf - -C "/usr/local/bin" && \
    apk del --no-cache "wget"

# install already built Ultimate WebBackend product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_OUTPUT_BUILD}/UWebBackend-linux" "${USER_HOME}"

# run the Ultimate WebBackend product as non-root user
USER "${USER_NAME}"

# add configuration files and templates for 'dockerize' and Ultimate
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build-products "${DIR_WEBSITE_CONFIG}/backend/settings_whitelist.json" "${USER_HOME}/settings_whitelist.json"
ADD "web.config.properties.tpl" "${USER_HOME}/web.config.properties.tpl"
ADD "WebBackend.ini.tpl" "${USER_HOME}/WebBackend.ini.tpl"
RUN rm -f "${USER_HOME}/WebBackend.ini"

ENV ULTIMATE_BACKEND_SETTINGS_WHITELIST="${USER_HOME}/settings_whitelist.json"
ENV ULTIMATE_BACKEND_SETTINGS_FILE="${USER_HOME}/web.config.properties"

# Serving the frontend from the backend is not supported by this Docker image
ENV ULTIMATE_FRONTEND_SERVE="False"
ENV ULTIMATE_FRONTEND_PATH="${USER_HOME}"
ENV ULTIMATE_FRONTEND_ROUTE="/website"

# expose communication port of the Webbackend
EXPOSE "${ULTIMATE_BACKEND_PORT}"

# define health check to supervise the Ultimate Webbackend's availability 
HEALTHCHECK --interval=1m --timeout=10s --start-period=20s \
    CMD curl -f "http://${ULTIMATE_BACKEND_HOST}:${ULTIMATE_BACKEND_PORT}${ULTIMATE_BACKEND_ROUTE}" || exit 1

# default entry point to automatically configure and start the Ultimate Webbackend product
ENTRYPOINT ["dockerize", "-template", "web.config.properties.tpl:web.config.properties", \
                         "-template", "WebBackend.ini.tpl:WebBackend.ini", \
                         "WebBackend"]
