var a : bool;
var b : bool;
procedure main() {
    var notA : bool;
    var notB : bool;
    var xOR : bool;
    var inEqual : bool;

    notA := !a;
    notB := !b;

    assert ((notA != a) && (notB != b));

    xOR := (a && !b) || (!a && b);
    inEqual := (a != b);

    assert (xOR == inEqual);
}