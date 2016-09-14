//

implementation main() returns (){
    var value : int;
    var y : int;
    var index : int;

    while (true)
    {
        call y := read(index);
        if (!(y >= 7)) {
            break;
        } 
        call value := read(index);
        a[index] := value - 1;
    }
    return;
}


var a : [int]int;

procedure read(#index : int) returns (#value : int);
ensures #value == a[#index];



procedure main() returns ();
modifies a;
