//#Unsafe
// Thread with no global writes; post-join must still be reachable.

procedure ULTIMATE.start()
{
    fork 1 noop();
    join 1;
    assert 0 == 1;
}

procedure noop()
{
}
