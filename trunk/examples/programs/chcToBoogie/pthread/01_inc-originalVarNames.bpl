//#Safe
/* Date: 2022-03-10
 * Author: Frank Schüssele
 *
 * Obtained from synthesis of correctness proof for pthread-ext/01_inc
 *
 */


procedure I(value : int, m : int, loc1 : int, v1 : int, loc2 : int, v2 : int) returns ()
{
    var tmp1 : int;
    var tmp2 : int;
    var tmp3 : int;

    if (*) {
        // Non-interference for lock();value:=v+1
        assume (m == 0 && tmp2 == 1) && value == tmp3 + 1;
        call I(tmp1, tmp2, loc1, v1, loc2, v2);
        call I(tmp1, tmp2, loc1, v1, 1, tmp3);
        call I(tmp1, tmp2, 1, tmp3, loc2, v2);
    } else if (*) {
        // Symmetry
        call I(value, m, loc2, v2, loc1, v1);
    } else if (*) {
        // Non-interference for v:=value;unlock()
        assume (m == 1 && tmp2 == value) && tmp3 == 0;
        call I(value, tmp3, 0, v1, loc2, v2);
        call I(value, tmp3, loc1, v1, 0, v2);
        call I(value, tmp3, loc1, v1, loc2, v2);
    } else if (*) {
        // Inductivity for v:=value;unlock()
        assume ((m == 1 && tmp3 == 0) && loc1 == 1) && v1 == value;
        call I(value, tmp3, 0, tmp2, loc2, v2);
    } else if (*) {
        // Initial location
        assume (m == 0 && loc1 == 0) && loc2 == 0;
    } else {
        // Inductivity for lock();value:=v+1
        assume ((m == 0 && value == v1 + 1) && tmp3 == 1) && loc1 == 2;
        call I(tmp2, tmp3, 1, v1, loc2, v2);
    }
}

procedure Ultimate.START() returns ()
{
    var value : int;
    var m : int;
    var v1 : int;
    var v2 : int;
    var loc2 : int;

    if (*) {
        assume !(v1 < value);
        call I(value, m, loc2, v2, 2, v1);
    } else {
        assume !(v1 < value);
        call I(value, m, 2, v1, loc2, v2);
    }
    assert false;
}

