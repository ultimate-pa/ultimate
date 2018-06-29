#!/bin/bash
#
# Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
#
# -----------------------------------------------------------------------------
#
# Creates a folder called '.settings' containing a file called
# 'org.sonarlint.eclipse.core.prefs' in all subfolders of the 'source' folder.
# The file will contain the following text:
#
# autoEnabled=XXX
# eclipse.preferences.version=1
# extraProperties=
# moduleKey=de.uni_freiburg.informatik.ultimate\:YYY
#
# where 'XXX' is either "true" or "false" 'YYY' is the name of the respective
# plugin.
# This will bind the plugin to the SonarQube server.
#
# -----------------------------------------------------------------------------
#
# Instructions:
# 1) Modify the variable 'ENABLE_ANALYSIS' according to your wishes.
# 2) Check that the variable 'PATH_TO_SOURCE' below is set correctly.
# 3) Run the script from its folder.
#
# -----------------------------------------------------------------------------

# Set this variable to either "false" or "true".
# "false": Do not automatically analyze this plugin with SonarLint.
# "true": Automatically analyze this plugin with SonarLint.
ENABLE_ANALYSIS="false"

if [[ $ENABLE_ANALYSIS == "" ]] ;
then
	echo "No option for variable 'ENABLE_ANALYSIS' set. Terminating..."
	exit
elif [[ $ENABLE_ANALYSIS != "true" && $ENABLE_ANALYSIS != "false" ]] ;
then
	echo "Illegal option for variable 'ENABLE_ANALYSIS' set. Terminating..."
	exit
fi

# This variable should point to the Ultimate source folder relative to the
# position from where the script is called.
PATH_TO_SOURCE="../../trunk/source/"

SETTINGS="/.settings"
FILE="$SETTINGS/org.sonarlint.eclipse.core.prefs"
MANIFEST="/META-INF/MANIFEST.MF"
PLUGIN_NAME_KEY="Bundle-SymbolicName: "

SONAR_API_TOKEN="1511b3e61939ae40e5624e01ad7e284e337de77b"


function check_key(){
    local search_string="$1"
    return `curl -qs -u ${SONAR_API_TOKEN}: \
    --data-urlencode "component=de.uni_freiburg.informatik.ultimate:${search_string}" \
    "https://monteverdi.informatik.uni-freiburg.de/sonar/api/components/show" | grep -c "not found"`
}

FAIL=()

for FOLDER in $(find $PATH_TO_SOURCE -maxdepth 1 -mindepth 1 -type d); do
	# exclude folders starting with '.'
	SHORT_NAME=$(basename "$FOLDER")
	echo "-- $SHORT_NAME --"
	if [[ "${SHORT_NAME:0:1}" != "." ]] ;
	then
		SETTINGS_FOLDER="$FOLDER$SETTINGS"
		# optionally create folder
		if [[ -e "$SETTINGS_FOLDER" ]] ;
		then
			echo "  folder $SETTINGS_FOLDER already exists"
		else
			echo "  creating folder $SETTINGS_FOLDER"
			mkdir "$SETTINGS_FOLDER"
		fi
		
		# optionally create file
		if [[ -e "$FOLDER$FILE" ]] ;
		then
			echo "  settings file already exists, overwriting..."
		else
			echo "  creating file $FOLDER$FILE"
			touch "$FOLDER$FILE"
		fi
		
		# find plugin name
		if [[ -e "$FOLDER$MANIFEST" ]] ;
		then
			PLUGIN_NAME=$(grep "$PLUGIN_NAME_KEY" "$FOLDER$MANIFEST" | sed "s/$PLUGIN_NAME_KEY//" | sed "s/;singleton:=true//")
			echo "  found plugin ID $PLUGIN_NAME"
			PLUGIN_ID="\nmoduleKey=de.uni_freiburg.informatik.ultimate\:$PLUGIN_NAME\nserverId=monteverdi.informatik.uni-freiburg.de"
            if ! check_key "$PLUGIN_NAME" ; then 
                echo "  Plugin $PLUGIN_NAME not found on sonar server"
                FAIL+=("$SHORT_NAME")
                continue 
            fi 
		else
			echo "  no MANIFEST.MF file found, cannot read the plugin ID"
            FAIL+=("$SHORT_NAME")
			PLUGIN_ID=""
            continue
		fi
		
		# write command
		echo -e "autoEnabled=$ENABLE_ANALYSIS\neclipse.preferences.version=1\nextraProperties=$PLUGIN_ID" > "$FOLDER$FILE"
	else
        FAIL+=("$SHORT_NAME")
		echo "  ignoring folder $FOLDER"
	fi
done

echo "Failed to write settings for the following folders:"
for i in  ${FAIL[@]} ; do echo "$i" ; done 