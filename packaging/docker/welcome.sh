#!/bin/sh

check_and_print_version() {
    for cmd in "${@}"; do
        if command -v "${cmd}" >/dev/null 2>&1; then
            "${cmd}" --version
            return
        fi
    done
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
