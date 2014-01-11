//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 6.10.2012

int g;

int stechelberg() {
  return 0;
}

int lauterbrunnen() {
    int nondet;
    if (nondet) {
        stechelberg();
    } else {
        stechelberg();
    }
    return 0;
}

int main() {
    int x;
    g = x;
    lauterbrunnen();
    //@ assert x != g;
}
