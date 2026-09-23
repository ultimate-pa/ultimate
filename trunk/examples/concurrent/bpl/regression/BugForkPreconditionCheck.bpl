//#Unsafe

/**
 * Date: 2026-09-22
 * Author: Dominik Klumpp (klumpp@lix.polytechnique.fr)
 *
 * Demonstrates a bug where the precondition of a forked procedure was not checked at the call site,
 * but assumed inside the procedure.
 * See <https://github.com/ultimate-pa/ultimate/issues/809> for details.
 */

procedure test(x : int)
requires false;
{
  assert false;
}

procedure ULTIMATE.start()
{
  fork 0 test(42);
  // call test(42);
}

