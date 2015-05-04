#!/usr/bin/perl -i
# In the bash shell you can apply this script to all files in the folder using the
# for i in *.smt2 ; do perl THIS_SCRIPT.pl $i; done

while (<>) {
  if (/^\(set-info :category \"industrial\"\)/) {
    print $_;
    print "(set-info :status unsat)\n"
  } else {
    print $_;
  }
}
