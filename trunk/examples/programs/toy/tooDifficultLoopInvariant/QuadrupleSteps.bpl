procedure main() returns ()
{
    var i : int;
    var length : int;

	assume length == 4192;
    i := 0;
    while (true)
    {
		assert i + 4 <= length;
        if (i >= 16768) {
            break;
        } 
		i := i + 4;
    }
}
