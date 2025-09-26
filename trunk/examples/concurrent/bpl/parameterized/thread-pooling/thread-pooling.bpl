//#Safe
// Source: https://dl.acm.org/doi/10.1145/2676726.2677012

var len : int; // total number of tasks
var tasks : [int]int; // array of tasks
var next : int; // position of next available task block
var m : bool; // lock protecting next

procedure ULTIMATE.start()
modifies next, m, tasks;
{
    var c : int; // position of current task
    var end : int; // position of last task in acquired block

    var x : int; // local variable for task processing

    // acquire block of tasks
    atomic { assume m == false; m := true; } // lock(m)
    c := next;
    next := next + 10;
    if (next <= len) {
        end := next;
    } else {
        end := len;
    }
    m := false; // unlock(m)

    // perform block of tasks
    while (c < end) {
        tasks[c] := 0; // mark task c as started

        // work on task c
        x := c;
        x := x + 1;
        x := x + 1;
        x := x + 1;
        x := x + 1;
        x := x + 1;
        x := x + 1;
        x := x + 1;

        tasks[c] := 1; // mark task c as finished
        assert tasks[c] == 1; // no other thread has started task c
        c := c + 1;
    }
}
