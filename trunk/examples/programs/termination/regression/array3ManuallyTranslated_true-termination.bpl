//#terminating
/*
 * Date: November 2013
 * Author: heizmann@informatik.uni-freiburg.de
 * Program array3 from terminator examples translated to boogie an simplified (manually).
 * Deterministic automaton does not work, because variables are havoced on the
 * second statement of the trace.
 *
 */

    var x : int;
    var y : int;
    var z : int;


implementation main() returns (#res : int)
{
    goto loc_6;
  loc_6:
    if (*) {
        goto loc_5;
    }
    goto end;
  loc_CP_1:
    if (*) {
        goto loc_3;
    }
    goto end;
  loc_CP_2:
    if (*) {
        goto loc_0;
    }
    goto end;
  loc_0:
    if (*) {
        if (!(50 <= y)) {
            goto end;
        }
        x := 0;
        goto loc_CP_1;
    }
    if (*) {
        if (!(1 + y <= 50)) {
            goto end;
        }
        y := 1 + y;
        goto loc_CP_2;
    }
    goto end;
  loc_3:
    if (*) {
        if (!(50 <= x)) {
            goto end;
        }
        goto loc_4;
    }
    if (*) {
        if (!(1 + x <= 50)) {
            goto end;
        }
        x := 1 + x;
        goto loc_CP_1;
    }
    goto end;
  loc_5:
    if (*) {
        x := 0;
        havoc z;
        y := 0;
        goto loc_CP_2;
    }
    goto end;
  loc_4:
  end:
}

procedure main() returns (#res : int);
    modifies x,y,z;

