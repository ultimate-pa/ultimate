#!/bin/bash
# Script that processes Dirks SV-COMP emails
# Expects a path to a file containing the email as first argument.

if [ -z "${1}" ] ; then
    echo "Specify path to file with email"
    exit 1
fi

get_unsounds="/storage/repos/ultimate/releaseScripts/benchmark-processing/getunsounds.py"
move_unsounds="/storage/tmp/svcomp2025logs/move-unsounds.sh"
svcomp="svcomp25"

mail=$(readlink -f "${1}")
timestamp=$(date +%Y%m%d_%H%M)
tool=$(grep -oP "results for tool \K\w+" "${mail}" | tr '[:upper:]' '[:lower:]')
tool="${tool:1}"

case $tool in
   gemcutter|automizer|kojak|taipan)
     ;;
   *)
     echo "$tool is not a valid tool" ; exit 1;;
esac

tmp_dir="${timestamp}_${tool}"
script_log="log_${timestamp}_${tool}"
touch "${script_log}"
script_log=$(readlink -f "${script_log}")

echo "Processing $tool for $timestamp by parsing $mail"
mkdir "$tmp_dir" > /dev/null

pushd "$tmp_dir" > /dev/null || exit 1
xmls="${tool}_${timestamp}_urls"
latest_run=$(grep -oP '.*xml.bz2' "${mail}" | grep -vi broken | grep -oP "\d+-\d+-\d+_\d+-\d+-\d+" | awk '!p[$0]++' |sort | tail -n1)
grep -oP "^https.*${latest_run}.*xml.bz2" "${mail}" | grep -vi broken | sort | uniq | grep -v "merged.xml.bz2" > "${xmls}"
if [ ! -s "${xmls}" ] ; then
  echo "There are no .xml files for the latest run ${latest_run}, exiting"
  exit 1
fi

echo "Downloading XMLs and extracting unsounds"
cat "${xmls}"
unsounds="${tool}_unsound"
"${get_unsounds}" -f "${xmls}" -o "${unsounds}" -d . >> "${script_log}"

echo "Download Logfiles"
grep -oP "^https.*${latest_run}.logfiles.zip" < "${mail}" | while IFS= read -r l ; do
  echo "Downloading $l"
  wget "${l}" >> "${script_log}"
  unzip "*.zip" >> "${script_log}"
done
rm "${xmls}"

echo "Copy mail"
cp "${mail}" .

# echo "Download HTML Tables"
# for l in $(grep -oP ^.*${latest_run}.*table.html "${mail}") ; do 
#   wget "${l}" >> "${script_log}"
# done


echo "Post-process"
"${move_unsounds}"
popd > /dev/null || exit 1

move-benchexec-results "${tmp_dir}" "${svcomp}-${tool}"
#rm -r "${tmp_dir}"
