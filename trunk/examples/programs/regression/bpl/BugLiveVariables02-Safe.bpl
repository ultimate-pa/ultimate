//#Safe
/**
This is an example, where the equality of a is needed in order to be able to
prove the validity of the assertion.

Edit: Currently, this example reveals a bug in RelevanVariables.

Author: musab@informatik.uni-freiburg.de
*/
implementation main() returns ()
{
    var a,i : int;
    assume(a == 0);

    while(*) {
	i := i + 1;
    }
    assert a == 0;
}

procedure main() returns ();
