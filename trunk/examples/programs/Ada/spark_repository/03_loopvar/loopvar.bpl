procedure Loopvar() {
    var x: int;
    x := 1;

    while (x < 10) {
        x := x + 1;
        assert x > 0;
    }
}
