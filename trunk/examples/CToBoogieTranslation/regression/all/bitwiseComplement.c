/*
  Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
  Date: 2022-11-30
*/

int main() {
    int i;
    unsigned int u;

    i = ~0;
    i = ~(-5);
    i = ~2147483647;
    i = ~(-2147483648);
    i = ~i;
    
    u = ~(0U);
    u = ~(4294967295U);
    u = ~(3U);
    u = ~u;
}
