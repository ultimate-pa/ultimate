/* Important property on simple bufferoverflow example
 * Security
 * 
 * Author: Numair Mansur (mansurm@informatik.uni-freiburg.de)
 * Date: 2018-04-30
 */

int get_location(void);
int get_value(void);

void main(void) {
	int age[10];
	int location,value, r;
	value = get_value(); // from user
	location = get_location(); // from user
	if(location >=0 && location <=10){
		age[location] = value;
	}
}
