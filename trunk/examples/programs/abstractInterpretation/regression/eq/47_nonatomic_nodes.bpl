//#Safe
/*
 * inspired by test "eq-assertionfail.c" (comitted at 12.10.2017)
 */ 
procedure main() returns () {
    var ~k~1 : int;

    if (!(0 <= ~k~1)) {
    }
    havoc ~k~1;
}

