package local.stalin.smt.dpll;

import java.util.HashSet;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;

public abstract class DPLLAtom extends Literal implements Comparable<DPLLAtom> {
	static class NegLiteral extends Literal {
		public NegLiteral(DPLLAtom atom) {
			this.atom = atom;
			this.negated = atom;
		}
		public int getSign() {
			return -1;
		}
		public String toString() {
			return atom.toStringNegated();
		}
		public Formula getSMTFormula(Theory smtTheory) {
			return atom.getNegatedSMTFormula(smtTheory);
		}
	}
	

	/**
	 * The number of the last formula that contains this
	 * atom (for interpolation).
	 * This is -1, if the atom is not used in any formula, but stems from
	 * global theory atoms.
	 */
	int decideLevel;
	Literal decideStatus;
	Literal lastStatus;
	double  activity;
	Object  explanation;
	SimpleList<Clause.Watcher> backtrackWatchers = new SimpleList<Clause.Watcher>();
	Set<TermVariable> instantiationVars;
	
	public DPLLAtom() {
		this.atom = this;
		this.negated = new NegLiteral(this);
	}

	/**
	 * Compares two atoms with respect to their activity. Do not override!
	 */
	public final int compareTo(DPLLAtom other) {
		return activity < other.activity ? 1
				: activity == other.activity ? hash - other.hash : -1;
	}

	/**
	 * Returns 1, since an atom is always positive.
	 */
	public int getSign() {
		return 1;
	}
	
	public final int getDecideLevel() { 
		return decideLevel;
	}

	/**
	 * Returns a string representation of the negated atoms.
	 * Subclasses may overwrite this for pretty output.
	 */
	public String toStringNegated() {
		return "!("+toString()+")";
	}
	
	/**
	 * Returns a SMT formula representing the negated atoms.
	 * Subclasses may overwrite this for pretty output.
	 */
	public Formula getNegatedSMTFormula(Theory smtTheory) {
		return smtTheory.not(getSMTFormula(smtTheory));
	}

	/**
	 * Returns the status of an atom:
	 * null if atom is undecided,
	 * atom if atom should be true,
	 * atom.negate() if atom should be false.
	 */
	public Literal getDecideStatus() {
		return decideStatus;
	}

	public abstract int getFirstFormulaNr();

	public abstract int getLastFormulaNr();

	// Returns 1 iff this atom contains t.
	public abstract int containsTerm(Term t);
	
	public void setInstantiationVariables(Set<TermVariable> instvars) {
		instantiationVars = instvars;
	}
	public Set<TermVariable> getInstantiationVariables() {
		return instantiationVars;
	}

	public void addInstantiationVariable(TermVariable tv) {
		if (instantiationVars == null)
			instantiationVars = new HashSet<TermVariable>();
		instantiationVars.add(tv);
	}
}
