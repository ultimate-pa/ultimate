int power(int base, int exponent) {           
    if (exponent <= 0) {
        return 1;
    } else if (exponent == 1) {
        return base;
    } else if (base == 2) {
        return base << (exponent-1);
    } else if (exponent % 2 == 1) {
        return base * power(base, exponent-1);
    } else {
        int halfPower = power(base, exponent/2);
        return halfPower * halfPower;
    }
}
