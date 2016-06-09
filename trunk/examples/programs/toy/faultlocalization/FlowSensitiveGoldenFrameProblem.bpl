// Date: 2016-04-28
// Christian, Numair, Matthias

// Program where we have golden frame for "havoc a" only in flow 
// sensitive analysis
// 
// Output of relevance analysis
//
// [L25]             *   size := 1;
//        VAL            [size=1]
// [L26]             %   havoc a;
//        VAL            [size=1]
// [L27]  COND TRUE  -   0 < size
//        VAL            [size=1]
// [L29]             *#  a := nondet;
//        VAL            [a=0, nondet=0, size=1]
// [L31]             -   assert a > 23;
//        VAL            [a=0, nondet=0, size=1]

procedure main() returns (){
    var nondet : int;
    var size : int;
    var a : int;

    size := 1;
    havoc a;
    if (0 < size)
    {
        a := nondet;
    }
    assert (a > 23);
}



