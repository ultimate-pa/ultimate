// 2014-11-13, Matthias Heizmann
// Output of our CACSL2Boogie translator for the following program where each 
// procedure except main has been removed.
// PodelskiRybalchenko-TACAS2011-Fig3_true-termination.c
//

implementation main() returns (#res : int){
    var #t~nondet0 : int;
    var #t~nondet1 : int;
    var #t~nondet2 : int;
    var ~old_x~3 : int;
    var ~old_y~3 : int;
    var ~x~2 : int;
    var ~y~2 : int;

    ~x~2 := #t~nondet0;
    havoc #t~nondet0;
    ~y~2 := #t~nondet1;
    havoc #t~nondet1;
    while (true)
    {
      Loop~0:
        if (!(~x~2 > 0 && ~y~2 > 0)) {
            break;
        }
        ~old_x~3 := ~x~2;
        ~old_y~3 := ~y~2;
        if (#t~nondet2 != 0) {
            havoc #t~nondet2;
            ~x~2 := ~old_x~3 - 1;
            ~y~2 := ~old_x~3;
        } else {
            havoc #t~nondet2;
            ~x~2 := ~old_y~3 - 2;
            ~y~2 := ~old_x~3 + 1;
        }
    }
    #res := 0;
    return;
}

procedure main() returns (#res : int);
modifies ;

