//#Safe
/*
 * author: nutz, 29.04.2014
 * topic: continue statement
 */
int main() {
	int k = 0;
	int i = 0;
	while (i < 5) {
		i++;
		if (i ==2) {
			continue;
		}
		k++;
	}
	//@assert k == 4;
	i = 0;
	k = 0;
	do {
		i++;
		if (i ==2) {
			continue;
		}
		k++;
	} while (i < 5);
	//@assert k == 4;
	for (int j = 0; j < 5; j++) {
		if (j ==2) {
			 continue;
		}
		k = j;
	}
	//@ assert k = 4;
}


