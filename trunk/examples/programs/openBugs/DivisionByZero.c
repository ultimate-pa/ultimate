// Author: heizmann@informatik.uni-freiburg.de
// Date: 30.12.2014
// I don't know if we want to classify this program safe or not because the
// integer division by zero is undefined behavior.

int main() {
    int x = 23 / 0;
}
