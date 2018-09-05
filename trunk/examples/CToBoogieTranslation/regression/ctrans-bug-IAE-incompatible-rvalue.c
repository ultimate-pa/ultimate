/*
2017-07-30: Example for java.lang.IllegalArgumentException: The value of the constructed RValue has a BoogieType ([int]int) that is incompatible with its CType ($Pointer$).
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml
-s ../../../trunk/examples/settings/default/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Default.epf

Author: Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
*/

int _oledbuffer[1];
void  oledGetBuffer()
{
 int* x = _oledbuffer;
 return;
}
