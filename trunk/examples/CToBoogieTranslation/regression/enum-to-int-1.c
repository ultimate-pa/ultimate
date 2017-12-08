//#Safe
/*
DD 2017-12-06

Leads to empty stack exception in CACSL2Boogie 

(further minimized by AN)
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

struct the_struct my_struct[SECOND];

int main(){
  my_struct[0];
}
