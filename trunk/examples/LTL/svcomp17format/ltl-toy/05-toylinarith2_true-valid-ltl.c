extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern unsigned int __VERIFIER_nondet_unsigned() __attribute__ ((__noreturn__));


unsigned int c ;
unsigned int servers ;
unsigned int resp;
unsigned int curr_serv;
unsigned int serversdiv2 ;

// Initialization routine
int __INITIALIZED = 0;
void env_init() {
	c =  __VERIFIER_nondet_unsigned();
	servers = __VERIFIER_nondet_unsigned();
	serversdiv2 = __VERIFIER_nondet_unsigned();

	__INITIALIZED = 1;
}

int main() {
	env_init();
	__VERIFIER_assume(servers>0 && c > 0); 

	if(__VERIFIER_nondet_unsigned())
		__VERIFIER_assume(serversdiv2+serversdiv2==servers);
	else
		__VERIFIER_assume(serversdiv2+serversdiv2+1==servers);
	resp = 0;
	curr_serv = servers;
  
  
	while(curr_serv > 0) {
		if(__VERIFIER_nondet_unsigned()) {
			c--; curr_serv--;
			resp++;
		} else {
			__VERIFIER_assume(c < curr_serv);
			curr_serv--;
		}
	}
}
