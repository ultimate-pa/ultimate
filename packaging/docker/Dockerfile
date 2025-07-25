#------------------------------------------------------------------------------
# Dockerfile: compile and package Ultimate toolchains
#------------------------------------------------------------------------------
# Author: Manuel Bentele
# Copyright (c) 2023
#------------------------------------------------------------------------------
# common build arguments for multi-staged Docker build
#------------------------------------------------------------------------------
ARG REPO_MAVEN_ROOT="trunk/source/BA_MavenParentUltimate"
ARG REPO_DIR_BUILD="trunk/source/BA_SiteRepository/target/products"
ARG REPO_DIR_TOOLS="releaseScripts/default/adds"
ARG DIR_BUILD="/home/build"
ARG DIR_ULTIMATE="${DIR_BUILD}/ultimate"
ARG DIR_OUTPUT="${DIR_ULTIMATE}/${REPO_DIR_BUILD}"
ARG DIR_TOOLS="${DIR_ULTIMATE}/${REPO_DIR_TOOLS}"
ARG USER_NAME="ultimate"
ARG USER_GROUP="ultimate"
ARG USER_HOME="/home/${USER_NAME}"

#------------------------------------------------------------------------------
# 1st build stage: compile and materialize Ultimate
#------------------------------------------------------------------------------
FROM alpine:3 AS build

ARG REPO_URL="https://github.com/ultimate-pa/ultimate.git"
ARG REPO_BRANCH="dev"

ARG REPO_MAVEN_ROOT
ARG REPO_DIR_BUILD
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT

# install build dependencies for an entire Ultimate build
RUN apk add --no-cache "git" \
                       "maven" \
                       "openjdk21"

# clone fresh Ultimate Git repository
RUN mkdir -p "${DIR_BUILD}" && \
    git clone --depth=1 --branch="${REPO_BRANCH}" "${REPO_URL}" "${DIR_ULTIMATE}"

# build all Ultimate products
WORKDIR "${DIR_ULTIMATE}"
RUN mvn -f "${REPO_MAVEN_ROOT}" clean package -P materialize

#------------------------------------------------------------------------------
# 2nd build stage: package common Ultimate artifacts shared by all products
#------------------------------------------------------------------------------
FROM alpine:3 AS ultimate-common

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT
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

# install alread compiled tools for all Ultimate products
COPY --from=build "${DIR_TOOLS}/cvc4" "/usr/bin/cvc4"
COPY --from=build "${DIR_TOOLS}/ltl2ba" "/usr/bin/ltl2ba"
COPY --from=build "${DIR_TOOLS}/mathsat" "/usr/bin/mathsat"
COPY --from=build "${DIR_TOOLS}/z3" "/usr/bin/z3"

# add Welcome script to print Ultimate version
ADD "welcome.sh" "/etc/profile.d/welcome.sh"

#------------------------------------------------------------------------------
# 3rd build stage: package Ultimate CLI
#------------------------------------------------------------------------------
FROM ultimate-common AS ultimate-cli

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate CLI product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build "${DIR_OUTPUT}/CLI-E4/linux/gtk/x86_64" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "/usr/bin/Ultimate"

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
ARG DIR_OUTPUT
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
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build "${DIR_OUTPUT}/Debug-E4/linux/gtk/x86_64" "${USER_HOME}"
RUN ln -s "${USER_HOME}/UltimateDebug" "/usr/bin/UltimateDebug"

# run the Ultimate Debug UI product as non-root user
#USER "${USER_NAME}"

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
ARG DIR_OUTPUT
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate ReqAnalyzer product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build "${DIR_OUTPUT}/ReqAnalyzer/linux/gtk/x86_64" "${USER_HOME}"
RUN ln -s "${USER_HOME}/ReqAnalyzer" "/usr/bin/ReqAnalyzer"

# run the Ultimate ReqAnalyzer product as non-root user
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
ARG DIR_OUTPUT
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate DeltaDebugger product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build "${DIR_OUTPUT}/DeltaDebugger/linux/gtk/x86_64" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "/usr/bin/Ultimate"

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
ARG DIR_OUTPUT
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

# install already built Ultimate Eliminator product
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build "${DIR_OUTPUT}/UltimateEliminator/linux/gtk/x86_64" "${USER_HOME}"
RUN ln -s "${USER_HOME}/Ultimate" "/usr/bin/Ultimate"

# run the Ultimate Eliminator product as non-root user
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
ARG DIR_OUTPUT
ARG DIR_TOOLS
ARG USER_NAME
ARG USER_GROUP
ARG USER_HOME

ARG REPO_DIR_WEBSITE_CONFIG="releaseScripts/website-config"
ARG DIR_WEBSITE_CONFIG="${DIR_ULTIMATE}/${REPO_DIR_WEBSITE_CONFIG}"

ENV ULTIMATE_BACKEND_HOST="localhost"
ENV ULTIMATE_BACKEND_PORT=8080
ENV ULTIMATE_BACKEND_ROUTE="/api"

ENV ULTIMATE_FRONTEND_SERVE="False"
ENV ULTIMATE_FRONTEND_PATH="/some/path"
ENV ULTIMATE_FRONTEND_ROUTE="/website"
ENV ULTIMATE_LOG_PATH="/dev/stdout"
ENV ULTIMATE_LOG_LEVEL="INFO"

ENV ULTIMATE_DIR_TMP="/tmp/ultimate"
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
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build "${DIR_OUTPUT}/WebBackend/linux/gtk/x86_64" "${USER_HOME}"
RUN ln -s "${USER_HOME}/WebBackend" "/usr/bin/WebBackend"

# run the Ultimate WebBackend product as non-root user
USER "${USER_NAME}"

# add configuration files and templates for 'dockerize' and Ultimate
COPY --chown="${USER_NAME}:${USER_GROUP}" --from=build "${DIR_WEBSITE_CONFIG}/backend/settings_whitelist.json" "${USER_HOME}/settings_whitelist.json"
ADD "web.config.properties.tpl" "${USER_HOME}/web.config.properties.tpl"
ADD "WebBackend.ini.tpl" "${USER_HOME}/WebBackend.ini.tpl"
RUN rm -f "${USER_HOME}/WebBackend.ini"

ENV ULTIMATE_BACKEND_SETTINGS_WHITELIST="${USER_HOME}/settings_whitelist.json"
ENV ULTIMATE_BACKEND_SETTINGS_FILE="${USER_HOME}/web.config.properties"

# expose communication port of the Webbackend
EXPOSE "${ULTIMATE_BACKEND_PORT}"

# define health check to supervise the Ultimate Webbackend's availability 
HEALTHCHECK --interval=1m --timeout=10s --start-period=20s \
    CMD curl -f "http://${ULTIMATE_BACKEND_HOST}:${ULTIMATE_BACKEND_PORT}${ULTIMATE_BACKEND_ROUTE}" || exit 1

# default entry point to automatically configure and start the Ultimate Webbackend product
ENTRYPOINT ["dockerize", "-template", "web.config.properties.tpl:web.config.properties", \
                         "-template", "WebBackend.ini.tpl:WebBackend.ini", \
                         "WebBackend"]
