/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * global struct initialization with pointer to itself
 */
struct list_head {
   struct list_head *next;
};

struct list_head s = { &s };

int main() {
    return 0;
}
