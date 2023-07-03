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

#------------------------------------------------------------------------------
# 1st build stage: compile and materialize Ultimate
#------------------------------------------------------------------------------
FROM debian:bullseye AS build

ARG REPO_URL="https://github.com/ultimate-pa/ultimate.git"
ARG REPO_BRANCH="dev"

ARG REPO_MAVEN_ROOT
ARG REPO_DIR_BUILD
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT

# install build dependencies for an entire Ultimate build
RUN apt-get update && \
    apt-get install -y "git" \
                       "maven" \
                       "openjdk-11-jdk" && \
    rm -rf /var/lib/apt/lists/*

# clone fresh Ultimate Git repository
RUN mkdir -p "${DIR_BUILD}" && \
    git clone --depth=1 --branch="${REPO_BRANCH}" "${REPO_URL}" "${DIR_ULTIMATE}"

# build all Ultimate products
WORKDIR "${DIR_ULTIMATE}"
RUN mvn -f "${REPO_MAVEN_ROOT}" clean package -P materialize

#------------------------------------------------------------------------------
# 2nd build stage: package Ultimate CLI
#------------------------------------------------------------------------------
FROM debian:bullseye AS ultimate-cli

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT
ARG DIR_TOOLS

# install runtime dependencies for Ultimate product
RUN apt-get update && \
    apt-get install -y "apt-utils" && \
    apt-get install -y "openjdk-11-jre" && \
    rm -rf /var/lib/apt/lists/*

# install already built Ultimate product
RUN mkdir -p "${DIR_ULTIMATE}"
WORKDIR "${DIR_ULTIMATE}"
COPY --from=build "${DIR_OUTPUT}/CLI-E4/linux/gtk/x86_64" "${DIR_ULTIMATE}"
RUN ln -s "${DIR_ULTIMATE}/Ultimate" "/usr/bin/Ultimate"

# install alread compiled tools for Ultimate
COPY --from=build "${DIR_TOOLS}/cvc4" "/usr/bin/cvc4"
COPY --from=build "${DIR_TOOLS}/ltl2ba" "/usr/bin/ltl2ba"
COPY --from=build "${DIR_TOOLS}/mathsat" "/usr/bin/mathsat"
COPY --from=build "${DIR_TOOLS}/z3" "/usr/bin/z3"

# default entry point to print installed Ultimate version
CMD ["Ultimate", "--version"]

#------------------------------------------------------------------------------
# 2nd build stage: package Ultimate Debug UI
#------------------------------------------------------------------------------
FROM debian:bullseye AS ultimate-debug

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT
ARG DIR_TOOLS

# install runtime dependencies for Ultimate product
RUN apt-get update && \
    apt-get install -y "apt-utils" && \
    apt-get install -y "openjdk-11-jre" && \
    rm -rf /var/lib/apt/lists/*

# install already built Ultimate product
RUN mkdir -p "${DIR_ULTIMATE}"
WORKDIR "${DIR_ULTIMATE}"
COPY --from=build "${DIR_OUTPUT}/Debug-E4/linux/gtk/x86_64" "${DIR_ULTIMATE}"
RUN ln -s "${DIR_ULTIMATE}/Ultimate" "/usr/bin/Ultimate"

# install alread compiled tools for Ultimate
COPY --from=build "${DIR_TOOLS}/cvc4" "/usr/bin/cvc4"
COPY --from=build "${DIR_TOOLS}/ltl2ba" "/usr/bin/ltl2ba"
COPY --from=build "${DIR_TOOLS}/mathsat" "/usr/bin/mathsat"
COPY --from=build "${DIR_TOOLS}/z3" "/usr/bin/z3"

# default entry point to print installed Ultimate version
CMD ["Ultimate", "--version"]

#------------------------------------------------------------------------------
# 2nd build stage: package Ultimate ReqAnalyzer
#------------------------------------------------------------------------------
FROM debian:bullseye AS ultimate-reqanalyzer

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT
ARG DIR_TOOLS

# install runtime dependencies for Ultimate product
RUN apt-get update && \
    apt-get install -y "apt-utils" && \
    apt-get install -y "openjdk-11-jre" && \
    rm -rf /var/lib/apt/lists/*

# install already built Ultimate product
RUN mkdir -p "${DIR_ULTIMATE}"
WORKDIR "${DIR_ULTIMATE}"
COPY --from=build "${DIR_OUTPUT}/ReqAnalyzer/linux/gtk/x86_64" "${DIR_ULTIMATE}"
RUN ln -s "${DIR_ULTIMATE}/Ultimate" "/usr/bin/Ultimate"

# install alread compiled tools for Ultimate
COPY --from=build "${DIR_TOOLS}/cvc4" "/usr/bin/cvc4"
COPY --from=build "${DIR_TOOLS}/ltl2ba" "/usr/bin/ltl2ba"
COPY --from=build "${DIR_TOOLS}/mathsat" "/usr/bin/mathsat"
COPY --from=build "${DIR_TOOLS}/z3" "/usr/bin/z3"

# default entry point to print installed Ultimate version
CMD ["Ultimate", "--version"]

#------------------------------------------------------------------------------
# 2nd build stage: package Ultimate DeltaDebugger
#------------------------------------------------------------------------------
FROM debian:bullseye AS ultimate-deltadebugger

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT
ARG DIR_TOOLS

# install runtime dependencies for Ultimate product
RUN apt-get update && \
    apt-get install -y "apt-utils" && \
    apt-get install -y "openjdk-11-jre" && \
    rm -rf /var/lib/apt/lists/*

# install already built Ultimate product
RUN mkdir -p "${DIR_ULTIMATE}"
WORKDIR "${DIR_ULTIMATE}"
COPY --from=build "${DIR_OUTPUT}/DeltaDebugger/linux/gtk/x86_64" "${DIR_ULTIMATE}"
RUN ln -s "${DIR_ULTIMATE}/Ultimate" "/usr/bin/Ultimate"

# install alread compiled tools for Ultimate
COPY --from=build "${DIR_TOOLS}/cvc4" "/usr/bin/cvc4"
COPY --from=build "${DIR_TOOLS}/ltl2ba" "/usr/bin/ltl2ba"
COPY --from=build "${DIR_TOOLS}/mathsat" "/usr/bin/mathsat"
COPY --from=build "${DIR_TOOLS}/z3" "/usr/bin/z3"

# default entry point to print installed Ultimate version
CMD ["Ultimate", "--version"]

#------------------------------------------------------------------------------
# 2nd build stage: package Ultimate Eliminator
#------------------------------------------------------------------------------
FROM debian:bullseye AS ultimate-eliminator

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT
ARG DIR_TOOLS

# install runtime dependencies for Ultimate product
RUN apt-get update && \
    apt-get install -y "apt-utils" && \
    apt-get install -y "openjdk-11-jre" && \
    rm -rf /var/lib/apt/lists/*

# install already built Ultimate product
RUN mkdir -p "${DIR_ULTIMATE}"
WORKDIR "${DIR_ULTIMATE}"
COPY --from=build "${DIR_OUTPUT}/UltimateEliminator/linux/gtk/x86_64" "${DIR_ULTIMATE}"
RUN ln -s "${DIR_ULTIMATE}/Ultimate" "/usr/bin/Ultimate"

# install alread compiled tools for Ultimate
COPY --from=build "${DIR_TOOLS}/cvc4" "/usr/bin/cvc4"
COPY --from=build "${DIR_TOOLS}/ltl2ba" "/usr/bin/ltl2ba"
COPY --from=build "${DIR_TOOLS}/mathsat" "/usr/bin/mathsat"
COPY --from=build "${DIR_TOOLS}/z3" "/usr/bin/z3"

# default entry point to print installed Ultimate version
CMD ["Ultimate", "--version"]

#------------------------------------------------------------------------------
# 2nd build stage: package Ultimate WebBackend
#------------------------------------------------------------------------------
FROM debian:bullseye AS ultimate-webbackend

ARG REPO_DIR_BUILD
ARG REPO_DIR_TOOLS
ARG DIR_BUILD
ARG DIR_ULTIMATE
ARG DIR_OUTPUT
ARG DIR_TOOLS

ARG REPO_DIR_WEBSITE_CONFIG="releaseScripts/website-config"
ARG DIR_WEBSITE_CONFIG="${DIR_ULTIMATE}/${REPO_DIR_WEBSITE_CONFIG}"

ENV ULTIMATE_DIR_TMP="/tmp/ultimate"

# install runtime dependencies for Ultimate product
RUN apt-get update && \
    apt-get install -y "apt-utils" && \
    apt-get install -y "openjdk-11-jre"

# install 'dockerize' for automatic configuration file creation
ENV DOCKERIZE_VERSION="v0.7.0"
RUN apt-get update && \
    apt-get install -y "wget" \
                       "curl" && \
    wget -O - "https://github.com/jwilder/dockerize/releases/download/${DOCKERIZE_VERSION}/dockerize-linux-amd64-${DOCKERIZE_VERSION}.tar.gz" | tar xzf - -C "/usr/local/bin" && \
    apt-get autoremove -yqq --purge "wget" && \
    rm -rf /var/lib/apt/lists/*

# install already built Ultimate product
RUN mkdir -p "${DIR_ULTIMATE}"
WORKDIR "${DIR_ULTIMATE}"
COPY --from=build "${DIR_OUTPUT}/WebBackend/linux/gtk/x86_64" "${DIR_ULTIMATE}"
RUN ln -s "${DIR_ULTIMATE}/Ultimate" "/usr/bin/Ultimate"

# install alread compiled tools for Ultimate
COPY --from=build "${DIR_TOOLS}/cvc4" "/usr/bin/cvc4"
COPY --from=build "${DIR_TOOLS}/ltl2ba" "/usr/bin/ltl2ba"
COPY --from=build "${DIR_TOOLS}/mathsat" "/usr/bin/mathsat"
COPY --from=build "${DIR_TOOLS}/z3" "/usr/bin/z3"

# add configuration files and templates for 'dockerize' and Ultimate
COPY --from=build "${DIR_WEBSITE_CONFIG}/backend/settings_whitelist.json" "${DIR_ULTIMATE}/settings_whitelist.json"
ADD "web.config.properties.tpl" "${DIR_ULTIMATE}/web.config.properties.tpl"
ENV ULTIMATE_BACKEND_SETTINGS_WHITELIST="${DIR_ULTIMATE}/settings_whitelist.json"

# activate Ultimate Webbackend configuration
RUN echo "-Dorg.eclipse.jetty.util.log.class=org.eclipse.jetty.util.log.StdErrLog" >> "${DIR_ULTIMATE}/Ultimate.ini" && \
    echo "-DWebBackend.SETTINGS_FILE=${DIR_ULTIMATE}/web.config.properties" >> "${DIR_ULTIMATE}/Ultimate.ini"

# create directory to store temporary files
RUN mkdir -p "${ULTIMATE_TMP_DIR}"

# expose communication port of the Webbackend
EXPOSE "${ULTIMATE_WEBBACKEND_PORT}"

# define health check to supervise the Ultimate Webbackend's availability 
HEALTHCHECK --interval=1m --timeout=10s --start-period=20s \
    CMD curl -f "http://${ULTIMATE_BACKEND_HOST}:${ULTIMATE_BACKEND_PORT}${ULTIMATE_BACKEND_ROUTE}" || exit 1

# default entry point to automatically configure and start the Ultimate Webbackend product
CMD dockerize -template "${DIR_ULTIMATE}/web.config.properties.tpl:${DIR_ULTIMATE}/web.config.properties" \
              -wait "tcp://${ULTIMATE_BACKEND_HOST}:${ULTIMATE_BACKEND_PORT}${ULTIMATE_BACKEND_ROUTE}" \
              -timeout "${ULTIMATE_BACKEND_START_TIMEOUT}" \
              Ultimate
