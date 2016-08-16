#!/usr/bin/perl

while(<>) {
    s!(f?printf\([^\(\)]*\))!/* $1 */!g;
    s!(fflush\([^\(\)]*\))!/* $1 */!g;
    s!(scanf\("%d", \&([a-zA-Z_]+)\);)!$2 = __VERIFIER_nondet_int(); /* $1 */!;
    print $_;
}
