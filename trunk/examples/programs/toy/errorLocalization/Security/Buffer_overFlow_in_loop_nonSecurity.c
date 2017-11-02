/* Buffer Overflow in loop
 * Non-Security
 * 
 * Author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
 * Date: 2017-10-30
 */

int get_age_from_user(void);
int f(void);

void main(void) {
	int age[ 1 ];
   	int i, temp, r;
   	r = f();        
   	for ( i = 0; i <= 2; i++ ) {
   		temp = get_age_from_user();
   		r = f();
   		if (r){
   			if (temp > 18){
   				age[i] = temp;	
   			}
   		}
    }
}
