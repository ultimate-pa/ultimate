// Date: 2016-04-28
// Christian, Numair, Matthias

// Program where we have golden frame for "havoc a" only in flow 
// sensitive analysis
// 
// Output of relevance analysis
//
// [L11]             *   size := 1;
//        VAL            [size=1]
// [L12]             %   havoc a;
//        VAL            [size=1]
// [L13]             *#  m := nondet0;
//        VAL            [m=0, nondet0=0, size=1]
// [L14]             *#  j := 0;
//        VAL            [j=0, m=0, nondet0=0, size=1]
// [L15]  COND TRUE  -   j < size
//        VAL            [j=0, m=0, nondet0=0, size=1]
// [L17]             *#  a[j] := nondet2;
//        VAL            [j=0, m=0, nondet0=0, nondet2=0, size=1]
// [L18]             -   j := j + 1;
//        VAL            [j=1, m=0, nondet0=0, nondet2=0, size=1]
// [L20]             -   assert a[0] > m;
//        VAL            [j=1, m=0, nondet0=0, nondet2=0, size=1]

procedure main() returns (){
    var nondet0 : int;
    var nondet2 : int;
    var size : int;
    var j : int;
    var a : [int]int;
    var m : int;

    size := 1;
    havoc a;
    m := nondet0;
    j := 0;
    if (j < size)
    {
        a[j] := nondet2;
        j :=  j + 1;
    }
    assert (a[0] > m);
}



