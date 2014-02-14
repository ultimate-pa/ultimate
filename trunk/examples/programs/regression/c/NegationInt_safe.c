//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 14.07.2013
// According to C99 !0 is exactly 1

int main() {
    int x = 0;
    int y = 1;
    int z = 2;
    int negX = !x;
    int negY = !y;
    int negZ = !z;
    //@ assert negX == 1 && negY == 0 && negZ == 0;
}
