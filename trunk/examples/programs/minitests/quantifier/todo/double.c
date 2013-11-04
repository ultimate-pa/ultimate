/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Double as struct field type
 * is not supported.
 */
struct str {
    double d;
};

int main() {
    struct str s;
    &s;

    return 0;
}
