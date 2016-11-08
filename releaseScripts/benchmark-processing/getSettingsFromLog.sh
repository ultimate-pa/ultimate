#!/bin/bash
grep -o 'Settings:.*epf' "${1}" | sort | uniq
