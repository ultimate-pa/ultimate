//#Unsafe
/* Bug reported by Elisabeth 
 * https://github.com/ultimate-pa/ultimate/issues/446
 * 
 * 
 * Author: Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Date: 2018-09-23
 * 
 */


//#Unsafe
procedure ULTIMATE.start()
{
    fork 1 foo();
    assert 0 == 1;
    join 1;
}

procedure foo()
{
}
