enum DAY /* Defines an enumeration type    */
{
	saturday, /* Names day and declares a       */
	sunday = 0, /* variable named workday with    */
	monday, /* that type                      */
	tuesday, wednesday, /* wednesday is associated with 3 */
	thursday, friday
} workday;

enum e_tag {
	a, b, c, d = 20, e, f, g = 20, h
} var;

int main() {
	enum DAY today = wednesday;

	enum BOOLEAN {
		false, true
	} end_flag;
	enum BOOLEAN match_flag;
	if (match_flag == false) {
		/* statement */
	}
	end_flag = true;

	//@ assert a == 0;
	//@ assert b == 1;
	//@ assert c == 2;
	//@ assert d == 20;
	//@ assert e == 21;
	//@ assert f == 22;
	//@ assert g == 20;
	//@ assert h == 21;
}
