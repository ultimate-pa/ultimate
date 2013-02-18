package local.stalin.smt.dpll;

import local.stalin.logic.Formula;

public abstract class Literal {
	DPLLAtom atom;
	Literal  negated;
	SimpleList<Clause.Watcher> watchers = new SimpleList<Clause.Watcher>();

	static int ctr = 0;
	int hash = ctr++;
	@Override
	public int hashCode() {
		return hash;
	}
	
	/**
	 * Returns the underlying atom.  If this literal is an atom, it returns itself.
	 */
	public final DPLLAtom getAtom() { return atom; }
	/**
	 * Returns the negated literal.
	 */
	public final Literal  negate()  { return negated; }
	/**
	 * Returns the sign of the literal (1 for atom, -1 for negated atom).
	 */
	public abstract int getSign();
	/**
	 * Returns a SMT representation of the literal.
	 * @return a SMT representation of the literal.
	 */
	public abstract Formula getSMTFormula(local.stalin.logic.Theory smtTheory);
}
