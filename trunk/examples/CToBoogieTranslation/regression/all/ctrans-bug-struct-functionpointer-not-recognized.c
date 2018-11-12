/*
 2017-12-15 Daniel Dietsch / Christian Schilling 
 
 We do not resolve the global function pointer *get() when it returns a struct. 
 Instead, we believe that the function get() is not defined. 
 
 */

struct foo {
	int a;
};

extern struct foo* get(void);

void main(void) {
	struct foo *my_foo = get();
    
}