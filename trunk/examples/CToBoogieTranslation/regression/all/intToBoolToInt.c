/*
 * author: nutz, 21.01.2014
 */

int main() {
	int i = 5;
	int j = 1;
	int false = 0;

	i = j >= 2;

	j = (1 && 2) != (i || j);//!= on two boogieBools

	j = (i++ && !1) + 3 && 3;
}
