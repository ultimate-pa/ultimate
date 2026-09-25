//#Unsafe

/**
 * Date: 2026-09-22
 * Author: Dominik Klumpp (klumpp@lix.polytechnique.fr)
 *
 * Demonstrates a bug in the computation of the condition to check at the call site.
 * See <https://github.com/ultimate-pa/ultimate/issues/810> for details.
 */

procedure test(x : int)
requires (forall foo : int :: x == foo);
{
  assert false;
}

procedure ULTIMATE.start()
{
  var foo : int;
  call test(foo);
}

