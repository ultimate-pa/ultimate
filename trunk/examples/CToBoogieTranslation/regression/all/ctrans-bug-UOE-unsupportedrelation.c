/*
2018-07-30: Minimal example for java.lang.UnsupportedOperationException: unsupported $Pointer$, INT
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml 
-s ../../../trunk/examples/settings/buchiAutomizer/termcomp2017-Noproofs.epf 

Author: Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
*/
void main(int *x) {
     0 < x ;
}

