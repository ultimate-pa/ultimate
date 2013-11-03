/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Since 's' is used with '&', it is translated to
 * a pointer. When '*p = s;' is translated, the auxiliary
 * variable has type integer instead of type pointer.
 */
struct str {
    int* i;
};

int main() {
    struct str s;
    struct str* p;
    p = &s;
    *p = s;
    
    return 0;
}
