/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * Struct in struct with an array does not work.
 */
struct inner {
   int arr[1];
};

struct outer {
   struct inner skey;
};

int main() {
    return 0;
}
