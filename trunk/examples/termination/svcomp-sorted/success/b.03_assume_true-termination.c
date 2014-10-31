extern int __VERIFIER_nondet_int(void);

int test_fun(int x, int y)
{
    if(x <= 0) {
       // replace assume
       return y;
    }

    while (x > y) {
       if(x <= 0) {
          // replace assume
          return y;
       }
       y = y + x;
    }
    return y;
}

int main() {
    return test_fun(__VERIFIER_nondet_int(), __VERIFIER_nondet_int());
}
