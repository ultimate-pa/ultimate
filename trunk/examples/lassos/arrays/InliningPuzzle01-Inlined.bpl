//#rTermination
/*
 * Date: 2016-09-14
 * Author: heizmann@informatik.uni-freiburg.de, schuessf@informatik.uni-freiburg.de
 * 
 */


var a : [int]int;

procedure read(#index : int) returns (#value : int);
ensures #value == a[#index];

procedure main() returns ();
modifies a;

implementation main() returns (){
    var value : int;
    var y : int;
    var index : int;
    var read_#index : int, read_#value : int;

    while (true)
    {
        read_#index := index;
        havoc read_#value;
        assume read_#value == a[read_#index];
        y := read_#value;
        if (!(y >= 7)) {
            break;
        }
        read_#index := index;
        havoc read_#value;
        assume read_#value == a[read_#index];
        value := read_#value;
        a[index] := value - 1;
    }
    return;
}

