int power (int base, int exponent)
{
    if (exponent == 0) {
        return 1;
    }
    else if (exponent == 1) {
        return base;
    }
    else if (base == 2) {
        return base << (exponent-1);
    }
    else {
        int result = 1;
        while (exponent > 0) {
            if (exponent % 2 == 1) {
                result *= base;
            }
            base *= base;
            exponent /= 2;
        }
        return result;
    }
}
