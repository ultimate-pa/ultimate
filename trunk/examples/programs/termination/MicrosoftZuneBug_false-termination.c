/*
 * Program similar to some code that was used once in Microsoft Zune
 * http://techcrunch.com/2008/12/31/zune-bug-explained-in-detail/
 * Date: 2014-07-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

extern int __VERIFIER_nondet_int(void);

int isLeapYear(int year) {
    if (year % 4 == 0) {
        if (year % 100 == 0)  {
            if (year % 400 == 0) {
                return 1;
            } else {
                return 0;
            }
        } else {
            return 1;
        }
    } else {
        return 0;
    }
}

int main() {
    int year = 1980;
    int days = __VERIFIER_nondet_int(); {
        if (days <0 || days > 366) {
            days = 0;
        }
    }
    while (days > 365)
    {
        if (isLeapYear(year))
        {
            if (days > 366)
            {
                days -= 366;
                year += 1;
            }
        }
        else
        {
            days -= 365;
            year += 1;
        }
    }
	return 0;
}
