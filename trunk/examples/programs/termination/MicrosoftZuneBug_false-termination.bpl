/*
 * Program similar to some code that was used once in Microsoft Zune
 * http://techcrunch.com/2008/12/31/zune-bug-explained-in-detail/
 * Date: 2014-07-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var year, days : int;


procedure isLeapYear(year : int) returns (res : bool)
{
    if (year % 4 == 0) {
        if (year % 100 == 0)  {
            if (year % 400 == 0) {
                res := true;
            } else {
                res := false;
            }
        } else {
            res := true;
        }
    } else {
        res := false;
    }
}

procedure main()
modifies year, days;
{
    var leapYear : bool;
    assume year >= 1980;
	assume days >= 0 && days <= 366;
    while (days > 365)
    {
	    call leapYear := isLeapYear(year);
        if (leapYear)
        {
            if (days > 366)
            {
                days := days - 366;
                year := year + 1;
            }
        }
        else
        {
            days := days - 365;
            year := year + 1;
        }
    }
}
