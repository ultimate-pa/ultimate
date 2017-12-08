//#Safe
/*
DD 2017-12-06

Leads to empty stack exception in CACSL2Boogie 

 */

#include <stdio.h>

enum the_enum {
 FIRST,
 SECOND
};

struct the_struct {
 unsigned int a;
 unsigned int b;
};

extern struct the_struct my_struct[SECOND];
struct the_struct my_struct[SECOND];

int main(){
  my_struct[0];// = { { 2, 4 } };
  //@assert my_struct[0].a == 0;
  return my_struct[0].a;
}
