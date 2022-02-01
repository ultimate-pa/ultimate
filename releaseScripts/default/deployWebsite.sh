#!/bin/bash
# Script that deploys a generated website and webeclipsebridge to the tomcat on this machine

### Settings
WARS=(
"../../trunk/source/BA_Website/target/Website.war"
"../../trunk/source/BA_Website/target/WebsiteEclipseBridge.war"
)

BACKUP_DIR="./war-backup"
TOMCAT_DIR="/var/lib/tomcat-8-ultimate"
TOMCAT_WEBAPP_DIR="${TOMCAT_DIR}/webapps/"
TOMCAT_CATALINA_DIR="${TOMCAT_DIR}/work/Catalina/"
TOMCAT_INIT_SCRIPT="/etc/init.d/tomcat-8-ultimate"

### ACTUAL SCRIPT
source /etc/init.d/functions.sh
DATE=`date +"%F %T"`

function exitOnFail {
    "$@"
    local status=$?
    if [ $status -ne 0 ]; then
		eerror "$@ failed with $1"
		eend $status
    fi
    eend $status
}

function checkFiles {
    for (( i = 0 ; i < ${#WARS[@]} ; i=$i+1 ));
    do
        local file="${WARS[${i}]}"
        ebegin "Checking $file"
        if [ ! -f "$file" ]; then
            eindent
            eerror ".war file $file does not exist"
            eoutdent
            eend 1
            return 1
        fi
        eend 0
    done
}

function backupWebsite {
    local backup="$BACKUP_DIR-$DATE"
    mkdir -p "$backup"
    for (( i = 0 ; i < ${#WARS[@]} ; i=$i+1 ));
    do
        local war="${WARS[${i}]}"
        local oldwar="$TOMCAT_WEBAPP_DIR"`basename "${war}"`
        local olddir="${oldwar%.war}"
        ebegin "Moving $oldwar to $backup"
        eindent
        if [ ! -f "$oldwar" ]; then
            ewarn "The old .war file $oldwar does not exist"
        else
            exitOnFail mv "$oldwar" "$backup"
        fi
        eoutdent
        eend 0
    done
}

function updateWebsite {
    for (( i = 0 ; i < ${#WARS[@]} ; i=$i+1 ));
    do
        local war="${WARS[${i}]}"
	local warnameonly=`basename "${war}"`
	local warnamenoext="${warnameonly%.war}"
        local oldwar="${TOMCAT_WEBAPP_DIR}${warnameonly}"
        local olddir="${oldwar%.war}"

        ebegin "Removing $olddir"
        eindent
        if [ ! -d "$olddir" ]; then
            ewarn "The old webapp directory $olddir does not exist"
        else 
            exitOnFail rm -r "$olddir"
        fi
        eoutdent
        eend 0

	for catdir in `find "$TOMCAT_CATALINA_DIR" -type d -name "$warnamenoext"` ; do
        	ebegin "Removing $catdir"
	        eindent
        	if [ ! -d "$catdir" ]; then
	            ewarn "The old local webapp directory $catdir does not exist"
        	else
	            exitOnFail rm -r "$catdir"
        	fi
	        eoutdent
	done

        ebegin "Copying $war to $oldwar"
        eindent
        exitOnFail cp "$war" "$oldwar"
        eoutdent
        eend 0
    done
}

function getRestoreDir {
    declare -n ret=$1
    number=1
    for file in "$BACKUP_DIR"*; do
        fnames+=("$file")
        echo "$number)" ${fnames[$(($number-1))]}
        let "number += 1"
    done
    read -p "Select a directory to restore: " fid
    fid=$(($fid-1)) # reduce user input by 1 since array starts counting from zero
    ret="${fnames[${fid}]}"
}

function runUpdate {
    checkFiles
    exitOnFail $TOMCAT_INIT_SCRIPT stop
    backupWebsite
    updateWebsite
    exitOnFail $TOMCAT_INIT_SCRIPT start
}

function revertFromLastBackup {
    getRestoreDir restoreDir
    WARS=("$restoreDir"/*)
    exitOnFail $TOMCAT_INIT_SCRIPT stop
    updateWebsite
    exitOnFail $TOMCAT_INIT_SCRIPT start
}

ARG_UPDATE=false
ARG_REVERT=false

while [[ $# -gt 0 ]]
do
    key="$1"
    case $key in
            -r|--revert)
            ARG_REVERT=true
            ;;
            -u|--update)
            ARG_UPDATE=true
            ;;
            *)
            # ignore unknown option
            echo "Unknown option $key"
            exit 1
            ;;
    esac
    shift # shift past argument or value
done

if [ "$ARG_UPDATE" = true ] && [ "$ARG_REVERT" = true ]; then 
    echo "You cannot combine update and revert"
    echo ""
elif [ "$ARG_UPDATE" = true ]; then 
    runUpdate
    exit 0
elif [ "$ARG_REVERT" = true ]; then 
    revertFromLastBackup
    exit 0
else
    echo "No arguments given"
fi 

echo "Usage:"
echo " -u|--update      updates the website"
echo " -r|--revert      reverts a backup from $BACKUP_DIR-*"
exit 1
