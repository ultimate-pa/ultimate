//#iSafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.2.2013


int g = 0;

int main() {
    int a = -1;
    a = proc();
    //@ assert a == 0 && g == 1;
   
}

int proc() {
  return g++;
}
