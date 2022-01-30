#!/usr/bin/perl -i
# Remove all (set-info ... ) commands, including these that use multiple lines.
#
# In the bash shell you can apply this script to all files in the folder using the
# for i in *.smt2 ; do perl removeSetInfo.pl $i; done



$multiLineSetInfo = 0;
while (<>) {
     if ($multiLineSetInfo && $_ =~ /^\|\).*/) {
         $multiLineSetInfo = 0;
         next;
     }
     if ($multiLineSetInfo) {
         next;
     }
     if ($_ =~ /^\(set-info :source \|.*/) {
          $multiLineSetInfo = 1;
          next;
     }
     next if $_ =~ /^\(set-info.*\)/;
     print $_;
}
