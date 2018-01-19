#!/bin/bash
# Script that deploys a generated website and webeclipsebridge to the tomcat on this machine 

### Settings
WARS=(
"../../trunk/source/BA_Website/target/Website.war"
"../../trunk/source/BA_Website/target/WebsiteEclipseBridge.war"
)

BACKUP_DIR="./war-backup"
TOMCAT_WEBAPP_DIR="/var/lib/tomcat-8-ultimate/webapps/"
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

function updateWebsite {
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
        
        ebegin "Removing $olddir"
        eindent
        if [ ! -d "$olddir" ]; then
            ewarn "The old webapp directory $olddir does not exist"
        else 
            exitOnFail rm -r "$olddir"
        fi
        eoutdent
        eend 0
        
        ebegin "Copying $war to $oldwar"
        eindent
        exitOnFail cp "$war" "$oldwar"
        eoutdent
        eend 0
    done
}

checkFiles
exitOnFail $TOMCAT_INIT_SCRIPT stop
updateWebsite
exitOnFail $TOMCAT_INIT_SCRIPT start

