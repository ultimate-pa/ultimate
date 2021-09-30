#!/bin/bash
# 
# Author: Nico Hauff (hauffn@informatik.uni-freiburg.de)

ultimate_dir="/mnt/Data/Developement/ultimate"
ultimate_adds_dir="${ultimate_dir}/releaseScripts/default/adds"
ultimate_maven_dir="${ultimate_dir}/trunk/source/BA_MavenParentUltimate"
ultimate_failure_paths_image_dir="${ultimate_dir}/trunk/examples/Requirements/failure-paths/img"
hanfor_dir="/mnt/Data/Developement/hanfor"
hanfor_pattern_dir="${hanfor_dir}/documentation/includes/patterns"
hanfor_failure_paths_image_dir="${hanfor_dir}/documentation/docs/img/failure_paths/positive"

run_req_checker_failure_path_generation=false
run_pea_to_dot=false

while getopts rp opt
do
   case $opt in
       r)  run_req_checker_failure_path_generation=true ;;
       p)  run_pea_to_dot=true ;;
       \?) echo "Invalid option: -$OPTARG" >&2 exit 1 ;;
       :)  echo "Option -$OPTARG requires an argument." >&2 exit 1 ;;
   esac
done

# Check if Ultimate adds directory is in PATH variable.
if ! echo $PATH | grep -q $ultimate_adds_dir
then
	echo "Could not find Ultimate adds directory in PATH."
	echo "Try: export PATH=\$PATH:$ultimate_adds_dir"
	exit 1
fi

# Check if branch is dev and is not dirty.
cd $ultimate_dir

current_branch=$(git branch --show-current)
if [ "$current_branch" != "dev" ]; then
	echo "Current branch must be 'dev', but it is: $current_branch"
	exit 1
fi

if ! git diff-index --quiet HEAD
then
	echo "Current branch is dirty."
	exit 1
fi


# Dump revision number to file.
git rev-parse HEAD > "${hanfor_pattern_dir}/ultimate_revision.txt"


# Uninstall Windows or format some hard drive. 
if $run_req_checker_failure_path_generation
then
	cd $ultimate_maven_dir
	echo "Current working directory:" $PWD
	echo "Run ReqCheckerFailurePathGenerationTestSuite ..."
	mvn clean integration-test -Pmanualtest -Dtest=ReqCheckerFailurePathGenerationTestSuite
fi

# Copy generated failure path images to hanfor docs.
if ls $ultimate_failure_paths_image_dir/*.svg &> /dev/null
then
	echo "Copy failure path image files to '$ultimate_failure_paths_image_dir' ..."
	rm $hanfor_failure_paths_image_dir/*.svg
	cp $ultimate_failure_paths_image_dir/*.svg $hanfor_failure_paths_image_dir
else
	echo "Could not find failure path image files in: $ultimate_failure_paths_image_dir"
	exit 1
fi

if $run_pea_to_dot
then
  	cd $ultimate_maven_dir
	echo "Current working directory:" $PWD
	echo "Run PeaToDotTestSuite ..."
	mvn clean integration-test -Pmanualtest -Dtest=PeaToDotTestSuite
fi

exit 0

