//#Safe
/* Date: 2022-03-15
 * Author: Frank Schüssele
 *
 * Obtained from synthesis of correctness proof for pthread-ext/01_inc
 *
 */


procedure I(value : int, m : int, loc1 : int, v1 : int, loc2 : int, v2 : int) returns ()
{
    var old_m : int;
    var old_v : int;
    var old_value : int;

    if (*) {
        // Non-interference for value:=v+1;unlock()
        assume m == 0 && old_m == 1 && value == old_v + 1;
        call I(old_value, old_m, loc1, v1, loc2, v2);
        call I(old_value, old_m, loc1, v1, 1, old_v);
        call I(old_value, old_m, 1, old_v, loc2, v2);
    } else if (*) {
        // Inductivity for value:=v2+1;unlock()
        assume m == 0 && old_m == 1 && loc2 == 2 && value == v2 + 1;
        call I(old_value, old_m, loc1, v1, 1, v2);
    } else if (*) {
        // Non-interference for lock();v:=value
        assume m == 1 && old_m == 0;
        call I(value, old_m, 0, v1, loc2, v2);
        call I(value, old_m, loc1, v1, 0, v2);
        call I(value, old_m, loc1, v1, loc2, v2);
    } else if (*) {
        // Inductivity for lock();v1:=value
        assume m == 1 && old_m == 0 && loc1 == 1 && v1 == value;
        call I(value, old_m, 0, old_v, loc2, v2);
    } else if (*) {
        // Inductivity for lock();v2:=value
        assume v2 == value && m == 1 && loc2 == 1 && old_m == 0;
        call I(value, old_m, loc1, v1, 0, old_v);
    } else if (*) {
        // Initial location
        assume m == 0 && loc1 == 0 && loc2 == 0;
    } else {
        // Inductivity for value:=v1+1;unlock()
        assume m == 0 && value == v1 + 1 && old_m == 1 && loc1 == 2;
        call I(old_value, old_m, 1, v1, loc2, v2);
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

