/*
2018-09-10: block level external linkage function declaration accessed via function pointer triggers assertion error (with -ea) 
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml 
-s ../../../trunk/examples/settings/default/automizer/svcomp-Reach-32bit-Automizer_Default.epf
*/
void foo()
{
  int x();
  (*x)();
}

