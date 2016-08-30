#!/bin/bash
echo "void reset_eca() {"
awk --posix 'BEGIN {FS=" "} 
     /^[ \t]*int.*=/ {var=$2; found=1; isarray=0}
     found && /\[\]/ {isarray=1; 
             initializer=$4; 
             gsub(/\{/,"",initializer);
             gsub(/\}\;/,"",initializer);
             gsub(/\[\]/,"",var)}
     (found && isarray) {split(initializer, initval, ","); 
                         idx=0;
                         for (val in initval) {
                                print var "[" idx "]=" initval[val] ";";
                                idx++;
                         }
                         found = 0;}
     (found && !isarray) {gsub(/\*/,"",var);
                          print var $3 $4; found = 0;}
     ' $1
echo "}"