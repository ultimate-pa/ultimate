int main() {
	int i = 0;
    int c = 0;
	while (i < 20) {
	    i++;
	    if (i <= 10) continue;
        c++;
	}
    return c;
}
