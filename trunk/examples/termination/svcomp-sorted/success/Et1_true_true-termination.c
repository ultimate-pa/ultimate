// public class Et1 {
    // public static void main(String[] args) {
		// Random.args = args;
	    // int a = - Random.random(); 
	   	// int b = - Random.random();	
	   	// loop(a,b);
	// }
	// public static void loop(int a, int b){
	   	// if (a > b) {
	   		// b = b + a;
 			// a = a + 1;
 			// loop(a,b);
	   	// }
    // }
// }
extern int __VERIFIER_nondet_int(void);
void loop(int a,int b);
int random(void);

int main() {
	int x = __VERIFIER_nondet_int();
	int y = __VERIFIER_nondet_int();
	int z = __VERIFIER_nondet_int();
	loop(-random(),-random());

}

int random() {
	int x = __VERIFIER_nondet_int();
	if (x < 0)
		return -x;
	else
		return x;
}

void loop(int a, int b){
	   	if (a > b) {
	   		b = b + a;
 			a = a + 1;
 			loop(a,b);
	   	}
}