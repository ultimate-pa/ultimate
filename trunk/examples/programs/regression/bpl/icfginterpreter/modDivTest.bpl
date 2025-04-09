procedure main() {
    var a : int;
    var b : int;
    var i : int;
    var j : int;
    havoc i;
    havoc j;
    assume j != 0;
    a := i / j;
    b := i % j;

    assert (a * j + b == i);
}