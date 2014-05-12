#!/usr/bin/perl -i
# Perl script that Jochen wrote for me to create .smt2 scripts for the 
# SMT competition
#
# In the bash shell you can apply this script to all files in the folder using the
# for i in *.smt2 ; do perl makeSmtCompCompatible.pl $i; done



#my $checksatseen = 0;
while (<>) {
     next if $_ =~ /^\(set-option :produce.*\)/;
     next if $_ =~ /^\(get-value\s.*\)/;
     next if $_ =~ /^\(echo .*\)/;
     next if $_ =~ /^\(get-unsat-core\)/;
#following is only needed if we want to remove multiple occrences of check-sat
#     if ($_ =~ /^\(check-sat\)/) {
#        next if $checksatseen;
#        $checksatseen = 1;
#     }
     print $_;
}
