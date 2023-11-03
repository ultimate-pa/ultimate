//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2022-11-22
//
// Invariants are shown at the wrong line number.


int data = 23;
int result = 48;

int main() {
    data = 0;
    while(1)
    {
        data = 2;
        break;
    }
    while(1)
    {
        result = data + 13;
        break;
    }
    //@ assert result == 15;
}
