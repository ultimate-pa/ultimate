#!/bin/bash
#
# Script for detecting obsolete settings in .epf files.
# Whenever you replace a setting add it to this file.
# This script should help in cases where one Ultimate developer renames
# settings on one branch and another Ultimate developer adds a new .epf
# file on another branch.
#
# 2025-07-09 Matthias Heizmann (matthias.heizmann@iste.uni-stuttgart.de)

echo "Checking .epf files in: $(pwd) for obsolete settings."


obsolete_settings=(
"/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Check\ array\ bounds\ for\ arrays\ that\ are\ off\ heap"
"/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Pointer\ base\ address\ is\ valid\ at\ dereference"
"/instance/de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator/Pointer\ to\ allocated\ memory\ at\ dereference"
)

find . -type f -name "*.epf" | while read -r file; do
    for obsolete_setting in "${obsolete_settings[@]}"; do
        if grep -Fq "$obsolete_setting" "$file"; then
            echo "ERROR: File '$file' contains obsolete setting: '$obsolete_setting'"
        fi
    done
done
