// #Safe
/* 
 * 
 * See InterproceduralProofRequired-Kandel.bpl
 * Here, we replace variable x by 7, hence we need do not need an
 * interprocedural proof.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2016-12-27
 *
 */

var g : int;

procedure inc() returns () 
modifies g;
{
    g := g + 1;
}


procedure main() returns ()
modifies g;
{
    var x : int;
    assume (g == 7);
    call inc();
    assert (g == 7 + 1);
}
