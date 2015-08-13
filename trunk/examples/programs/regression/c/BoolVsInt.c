//#Safe
/* conversion between integer and Boolean types */
int main()
{
    /* unary Boolean operator (negation) */
    
    int i = (0 == 0);
    i = !i;
    //@ assert i == 0;
    i = !i;
    //@ assert i != 0;
    i = !(!!(0 == !0));
    //@ assert i != 0;
    
    
    /* binary Boolean operators */
    
    
    i = (0 == 0);
    //@ assert i != 0;
    
    i = (0 != 0);
    //@ assert i == 0;
    
    i = (0 >= 0);
    //@ assert i != 0;
    
    i = (0 > 0);
    //@ assert i == 0;
    
    i = (0 <= 0);
    //@ assert i != 0;
    
    i = (0 < 0);
    //@ assert i == 0;
    
    
    /* logical AND/OR (expects Booleans) */
    
    
    i = 0;
    i = (0 == 0) && (0 != 0) && !i;
    //@ assert i == 0;
    i = !(0 + 1) || 0 || (1 == 1);
    //@ assert i == 1;
    
    
    /* if */
    
    
    i = 0;
    if (i) {
        i = 1;
    }
    //@ assert i == 0;
    
    i = 0;
    if (!i) {
        i = 1;
    }
    //@ assert i == 1;
    
    i = 0;
    if (0 == 0) {
        i = 1;
    }
    //@ assert i == 1;
    
    i = 0;
    if ((i == 0) && i) {
        i = 1;
    }
    //@ assert i == 0;
    
    i = 0;
    if (i + 1) {
        i = 1;
    }
    //@ assert i == 1;
    
    
    /* while / do-while */
    
    
    i = 2;
    while (i) {
        i = i - 1;
    }
    //@ assert i == 0;
    
    i = 2;
    while (0 == 0) {
        i = i - 1;
        break;
    }
    //@ assert i == 1;
    
    i = 2;
    while ((0 == 0) && i) {
        i = i - 1;
    }
    //@ assert i == 0;
    
    i = 2;
    do {
        i = i - 1;
    } while ((0 == 0) && i);
    //@ assert i == 0;
    
    
    return i;
}
