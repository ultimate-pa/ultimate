//#Safe
// Author: lindenmm@informatik.uni-freiburg.de
// Date: 16.08.2012

int u, h1, h2, e, r1, r2, i, c, m, f;

void unused() {
	u = 1;
}

void wait() {
	wait();
}

void handle() {
	h1 = 3;
	h2 = h1;
}

void exec();

void inc() {
	exec();
}

void respond() {
	r1 = 4;
	r2 = 7;
	inc();
}

void exec() {
	e = 5;
	wait();
	handle();
	respond();
}

void init() {
	i = 6;
}

void clean() {
	c = 7;
}

int main() {
	m = 8;
	init();
	exec();
	clean();
	main();
}

void main1();

/*@
 @ assigns u, h1, f;
 @*/
void finalize();

void finalize() {
	f=2;
	main1();
}

void main1() {
	finalize();
}
