/*
2018-09-10 DD: Example triggers ClassCastException: de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed cannot be cast to de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive
-tc ../../../trunk/examples/toolchains/CheckedCTranslation.xml
-s ../../../trunk/examples/settings/default/automizer/svcomp-DerefFreeMemtrack-32bit-Automizer_Bitvector.epf
*/

typedef long unsigned int __uint32_t;
typedef __uint32_t uint32_t ;

extern uint32_t random_uniform();

void random_permute()
{
  int j = random_uniform();
}

