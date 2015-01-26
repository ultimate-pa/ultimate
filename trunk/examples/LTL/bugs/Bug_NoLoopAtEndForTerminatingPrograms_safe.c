//#Safe
//
//@ ltl invariant positive: !<>AP(ap > 2);

int loop_counter;
int ap;

int main() {
  loop_counter = 1;
  ap = 0;

  while(loop_counter > 0) {
	  loop_counter--;
	  ap++; // ap == loop_counter
  }
}

