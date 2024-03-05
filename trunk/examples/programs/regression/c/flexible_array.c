//#Safe
/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2023-11-14
  
  sizeof for structs ignores flexible arrays, see https://en.cppreference.com/w/c/language/struct
*/

struct string {
  unsigned length;
  char data[];
};

int main() {
  unsigned size = sizeof(struct string);
  //@ assert size == 4;
}