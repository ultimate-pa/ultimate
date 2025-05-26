// #Safe
// Works with SequenceOfStatements setting

procedure main() returns (gdc : int) {
    var a : int;
    var b : int;
    var originalA : int;
    var originalB : int;
    havoc a;
    havoc b;
    assume (a > 0) && (b > 0);
    assert (a >= 0) && (b >= 0); // <- used to seperate the original_ assignment, dependent otherwise
    originalA := a;
    originalB := b;


    while(a != 0 && b != 0) {
        if(a > b) {
            a := a % b;
        } else {
            b := b % a;
        }
    }

    if(b == 0) {
        gdc := a;
    } else if (a == 0) {
        gdc := b;
    }

    assert gdc >= 0 && a + b == gdc;
    assert (originalA % gdc == 0) && (originalB % gdc == 0);
}