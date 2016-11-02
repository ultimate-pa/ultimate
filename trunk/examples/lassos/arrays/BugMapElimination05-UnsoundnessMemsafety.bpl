//#rNonTerminationDerivable
/*
 * Date: 2016-11-02
 * schuessf@informatik.uni-freiburg.de
 * 
 * Unsoundness (too strong result), extracted from:
 * svcomp/memsafety/test-0504_true-valid-memsafety.i
 */
 
var array : [int] int;

procedure ULTIMATE.start() returns ()
modifies array;
{
    call main();
}

procedure main() returns ()
modifies array;
{
    var res : int;
    while (true) {
        call res := getIndex();
    }
}

procedure getIndex() returns (index : int);
ensures old(array)[index] == 0;
ensures array == old(array)[index := 1];
modifies array;