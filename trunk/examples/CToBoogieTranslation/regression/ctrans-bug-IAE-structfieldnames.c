/*
 * Leads to java.lang.IllegalArgumentException: Field 'i' not in struct! exception CACSL2Boogie. 
 *
 * Author: dietsch@informatik.uni-freiburg.de 
 * 2018-07-01 
 */
int i;

struct mystruct {
 int i[1];
};

struct mystruct x;

void t1()
{
  x.i;
}

