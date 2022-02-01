//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.2.2013


int g = 0;

int proc() {
  return g++;
}

int main() {
    int a = -1;
    a = proc();
    //@ assert a == 0 && g == 1;
   
}

