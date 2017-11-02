/* Simple buffer overflow
 * Security
 * 
 * Author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
 * Date: 2017-10-30
 */

int get_location(void);
int get_value(void);
int f(void);

void main(void) {
	int age[10];
	int location,value;
	location = get_location(); // from user
	value = get_value(); // from user
	age[location] = value;
}
