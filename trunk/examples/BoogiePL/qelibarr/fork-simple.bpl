/*
 * Fork
 * Date: November 2016
 * Author: qelibarr@informatik.uni-freiburg.de
 */
procedure callee(b : int)
{
}

procedure main()
{
    fork callee(1);
}


procedure ULTIMATE.start()
{
    fork main();
}
