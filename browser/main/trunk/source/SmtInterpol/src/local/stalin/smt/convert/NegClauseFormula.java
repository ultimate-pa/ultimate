/**
 * 
 */
package local.stalin.smt.convert;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.smt.dpll.Literal;

class NegClauseFormula extends FlatFormula {
	/**
	 * 
	 */
	ClauseFormula positive;
	Formula smtFormula;
	boolean auxAxiomsAdded;

	NegClauseFormula(ConvertFormula convertFormula, ClauseFormula pos) {
		super(convertFormula);
		this.positive = pos;
	}
	public FlatFormula negate() {
		return positive;
	}
	
	public void addAuxAxioms(int formNumber) {
		HashSet<FlatFormula> clause = new HashSet<FlatFormula>();
		/* "!lit ==> !subformula"  is "(!sf1 || lit) && ... && (!sfn || lit)" */
		for (FlatFormula l: positive.subformulas) {
			clause.addAll(l.negate().getSubFormulas());
			Literal[] lits = new Literal[clause.size()+1];
			int dest = 0;
			lits[dest++] = positive.lit;
			for (FlatFormula ff : clause) {
				Literal lit = lits[dest++] = ff.getLiteral(formNumber);
				lit.getAtom().setInstantiationVariables(ff.termVariables);
			}
			converter.addClause(lits,formNumber);
			clause.clear();
		}
		auxAxiomsAdded = true;;
	}
	
	//@Override
	public void addAsAxiom(int formNumber) {
		for (FlatFormula l: positive.subformulas) {
			l.negate().addAsAxiom(formNumber);
		}
	}
	
	//@Override
	public Formula getSMTFormula() {
		if (smtFormula == null) {
			smtFormula = Atom.TRUE;
			for	(FlatFormula l: positive.subformulas)
				smtFormula = converter.dpllEngine.
					andFormula(l.negate().getSMTFormula(), smtFormula);
		}
		return smtFormula;
	}

	//@Override
	public Literal getLiteral(int formNumber) {
		if (positive.lit == null)
			positive.lit = this.converter.createAnonAtom(positive.getSMTFormula());
		positive.lit.occursIn(formNumber);
		if (!auxAxiomsAdded)
			addAuxAxioms(formNumber);
		return positive.lit.negate();
	}

	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula) this);
	}

	public String toString() {
		return "(NOT "+positive+")";
	}
}