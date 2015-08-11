//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 2015-08-11
// Obtained from Markus Lindenmann's enum example.

enum DAY /* Defines an enumeration type    */
{
	saturday, /* Names day and declares a       */
	sunday = 0, /* variable named workday with    */
	monday, /* that type                      */
	tuesday, wednesday, /* wednesday is associated with 3 */
	thursday, friday
} workday;

int main() {
	enum DAY today = wednesday;
	if (today != wednesday) {
		//@ assert \false;
	}
	if (wednesday != 3) {
		//@ assert \false;
	}
}