//#iUnsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;
int nondet;

int stechelberg() {
  return;
}

int lauterbrunnen() {
    if (nondet) {
        stechelberg();
    } else {
        stechelberg();
    }
    return;
}

int main() {
    int x;
    g = x;
    lauterbrunnen();
    //@ assert x != g;
}
