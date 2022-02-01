//#Safe
// Author: heizmann@informatik.uni-freiburg.de, Daniel Dietsch
// Date: 15.12.2014
// Integer division in C. Minimal example extracted from failed SV-COMP benchmark.

int main() {
   int a1 = 518104;
   a1 = (((((a1 % 25)- -13) - 42605) / 5) - -8517);
   //@ assert a1 == 0;
   return 0;
}