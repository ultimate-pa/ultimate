#!/bin/bash

# This script can be used to run individual unit tests from the command line,
# without the complex steps performed by maven for each run.
#
# This requires the JUnit console runner, which can e.g. be downloaded from
# https://repo1.maven.org/maven2/org/junit/platform/junit-platform-console-standalone/
# Place it in this directory and, if necessary, adjust the variable JUNIT_JAR below.
#
# Execute ./makeFresh.sh first, and then invoke this script as follows:
#
#  > ./run-test.sh <PROJECT> <CLASS> <TEST>
#
# where <PROJECT> is the Ultimate project where the test is located (e.g. "Library-TraceCheckerUtilsTest"),
# <CLASS> is the fully qualified name of the class (e.g. "de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.PetriOwickiGriesTestSuite"),
# and <TEST> is the name of the test case (i.e., method) that you want to run.
# In the case where the tests in <CLASS> are generated dynamically from files,
# make sure to replace any symbols not allowed in method names (e.g. "."),
# and use the resulting name of the test case (e.g. "test_ats" instead of "test.ats").

JUNIT_JAR="junit-platform-console-standalone-1.9.3.jar"

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

PROJECT=$1
CLASS=$2
FILE=$3
ASSERTIONS=$(if [[ -z $4 || "$4" == "true" ]]; then echo "-ea"; fi)

cd "$SCRIPT_DIR/../../trunk/source/$PROJECT"

METHOD=$(echo "$FILE" | tr . _)

# collect class paths for all Ultimate projects
PROJECT_CLASS_PATHS=($(for dir in "$SCRIPT_DIR/../../trunk/source/"*"/target/classes"; do echo "-cp"; echo "$dir"; done))

PATH="$PATH:$SCRIPT_DIR/adds" java $ASSERTIONS -jar "$SCRIPT_DIR/$JUNIT_JAR" ${PROJECT_CLASS_PATHS[@]} \
  -cp "$SCRIPT_DIR/../../trunk/source/BA_SiteRepository/target/repository/plugins/org.apache.commons.io_2.6.0.v20190123-2029.jar" \
  --select-method "$CLASS#$METHOD" --details=verbose

