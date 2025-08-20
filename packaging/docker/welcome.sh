#!/bin/sh

ULTIMATE_CONFIG_PATH="/home/ultimate/config"

check_and_print_version() {
    for cmd in "${@}"; do
        if command -v "${cmd}" >/dev/null 2>&1; then
            "${cmd}" --version
            return
        fi
    done
}

check_and_print_config() {
    if [ -d "${ULTIMATE_CONFIG_PATH}" ] && [ "$(ls -A "${ULTIMATE_CONFIG_PATH}")" ]; then
        export ULTIMATE_CONFIG_PATH="${ULTIMATE_CONFIG_PATH}"
        echo "Product-specific toolchain and setting files for Ultimate are available at: ${ULTIMATE_CONFIG_PATH}"
        echo "You can access the configuration directory via the environment variable 'ULTIMATE_CONFIG_PATH'."
    else
        echo "Product-specific toolchain and setting files for Ultimate are not part of this installation."
    fi
}

echo "▗▖ ▗▖▗▖ ▗▄▄▄▖▗▄▄▄▖▗▖  ▗▖ ▗▄▖▗▄▄▄▖▗▄▄▄▖"
echo "▐▌ ▐▌▐▌   █    █  ▐▛▚▞▜▌▐▌ ▐▌ █  ▐▌   "
echo "▐▌ ▐▌▐▌   █    █  ▐▌  ▐▌▐▛▀▜▌ █  ▐▛▀▀▘"
echo "▝▚▄▞▘▐▙▄▄▖█  ▗▄█▄▖▐▌  ▐▌▐▌ ▐▌ █  ▐▙▄▄▖"
echo "┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓"
echo "┃     Program Analysis Framework     ┃"
echo "┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛"
check_and_print_version "Ultimate" "UltimateDebug" "ReqAnalyzer" "WebBackend"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
check_and_print_config
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
