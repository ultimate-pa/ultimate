/*
 * Single-trace analyis computes assignment to x as aberrant
 * Multi-trace analysis computes assignment to y as aberrant
 *
 * Assuming the error trace takes the else branch of the conditional.
 * 
 * The reason for such a result is the lack of branching
 * information in the else branch.
 */


int get_x(void);
int get_y(void);

void main(void) {
	
	int x= get_x();
	int y = get_y();
	int z = 1;
	if (x==1) {
		if(y==2){
		}	
	}
	if(z == 1) __VERIFIER_error();

}
