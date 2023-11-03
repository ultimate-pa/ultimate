#!/usr/bin/perl -i
# Perl script that Jochen wrote for me.
# This script removes all commands enclosed by push-pop with one exception:
# The commands between that last push-pop at level 1 are not removed.
# I use this to create a script for a main track that is only compatible
# to the application track.
#
# In the bash shell you can apply this script to all files in the folder using the
# for i in *.smt2 ; do perl thisScript.pl $i; done

#my $checksatseen = 0;
my $level = 0;
while (<>) {
     if (/^\(push\s+(\d+)\)/) {
         $level += $1;
         $last = "";
         next;
     }
     if (/^\(pop\s+(\d+)\)/) {
         $level -= $1;
         next;
     }
     $last .= $_ if $level == 1;
     print $_ if $level == 0;
}
print $last;
