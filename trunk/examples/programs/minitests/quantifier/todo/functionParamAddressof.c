/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Function parameters are not correctly addressoffed.
 */
int func(int i1) {
    int* p;
    int i2;
    p = &i2; /* this works */
    p = &i1; /* this does not */
    
    return 0;
}

int main() {
    func(1);
    
    return 0;
}
