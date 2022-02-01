// *************************************************************
//
//     Branching-time reasoning for infinite-state systems
//
//              Byron Cook * Eric Koskinen
//                     July 2010
//
// *************************************************************

// Benchmark: acqrel.c
// Property: AG(a => AF r)

void init() { A = R = 0; }

int body() {
  while(nondet()) {
    A = 1;
    A = 0;
    n = nondet();
    while(n>0) {
      n--;
    }
    R = 1;
    R = 0;
  }
  while(1) { int x; x=x; }
  return 0;
}

int main() { }
