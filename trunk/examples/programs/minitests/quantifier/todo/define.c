/*
 * Date: November 2013
 * Author: Christian Schilling
 * 
 * #define is not resolved properly.
 * NOTE: The error is currently not the same as
 *       in the SV-COMP examples, but the general
 *       problem seems to be the same!?
 */
struct list_head {
   int i;
};

#define LIST_HEAD(name) \
	struct list_head name = { 1 }

int main() {
    LIST_HEAD(gl_list);
    
    return 0;
}
