#!/bin/bash 
# Script that allows you to compare a Jenkins Nightly Build run with a local regression test run
# 
# To run all regression tests locally:
# cd trunk/source/BA_MavenParentUltimate
# ...
# (wait for approx. 7h)
# Results are now in find trunk/source -ipath */surefire-reports/TEST*xml
# 

REPO_ROOT="/storage/repos/ultimate-2"
JENKINS_TEST_RESULTS="jenkins_latest_tests.xml"

OUT=$(mktemp -d) || { echo "Failed to create temp directory"; exit 1; }

pushd "$OUT" > /dev/null 2>&1

echo "Downloading Jenkins tests..."
curl -s -o "$JENKINS_TEST_RESULTS" 'https://monteverdi.informatik.uni-freiburg.de/ci/job/Ultimate%20Nightly/lastCompletedBuild/testReport/api/xml'
# # note, if you want to debug, use xmllint --format jenkins_latest_tests.xml > jenkins_latest_tests_formatted.xml 
xmllint --xpath '//status[text() = "FAILED" ]/preceding-sibling::name/text()' "$JENKINS_TEST_RESULTS" 2> /dev/null | sort > jenkins_failed

echo "Collating local test reports..."
for i in $(find "${REPO_ROOT}/trunk/source" -ipath */surefire-reports/TEST*xml) ; do 
  xmllint --xpath '//failure/parent::testcase/@name' "$i" 2> /dev/null | sed -e 's/"//g ; s/name=//g ; s/^[ \t]*//' >> local_failed
done 
cat local_failed | sort > lf 
mv lf local_failed

echo ""
echo "## Tests that fail local but not on Jenkins"
diff --new-line-format="" --unchanged-line-format="" local_failed jenkins_failed
echo ""
cat <<EOF
You can get more information about your local test failue by using 
TESTNAME="..." ; for i in \$(find "${REPO_ROOT}/trunk/source" -ipath */surefire-reports/TEST*xml) ; do if grep -q "\$TESTNAME" "\$i" ; then xmllint --xpath "//testcase[@name='\${TESTNAME}']" "\$i" | less ; fi ; done
EOF

popd "$OUT" > /dev/null 2>&1
rm -r "$OUT" || echo "Cleanup of $OUT failed!"


# while IFS= read -r line ; do
#   echo "$line"
#   xmllint --xpath "//testcase[@name='${line}']/failure" TEST-de.uni_freiburg.informatik.ultimate.regressiontest.generic.RegressionTestSuite.xml 
# done < new-local 