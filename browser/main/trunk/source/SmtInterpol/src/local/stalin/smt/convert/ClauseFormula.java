/**
 * 
 */
package local.stalin.smt.convert;

import java.util.Set;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.smt.dpll.Literal;
import local.stalin.smt.dpll.NamedAtom;

/**
 *  Represents a formula that is a (non-trivial) disjunction of flat formulas. 
 */
class ClauseFormula extends FlatFormula {
	Formula smtFormula;
	NamedAtom lit;
	NegClauseFormula negated;
	Set<FlatFormula> subformulas;
	boolean auxAxiomsAdded;
	
	public ClauseFormula(ConvertFormula converter, Set<FlatFormula> subformulas) {
		super(converter);
		negated = new NegClauseFormula(converter, this);
		this.subformulas = subformulas;
	}

	public FlatFormula negate() {
		return negated;
	}
	
	public void addAuxAxioms(int formNumber) {
		Literal[] lits = new Literal[subformulas.size()+1];
		/* "lit ==> subformula"  is "!lit || subformula" */
		lits[0] = lit.negate();
		int i = 1;
		for (FlatFormula l : subformulas) {
			Literal lit = lits[i++] = l.getLiteral(formNumber);
			lit.getAtom().setInstantiationVariables(l.termVariables);
		}
		converter.addClause(lits,formNumber);
		auxAxiomsAdded = true;
	}

	//@Override
	public void addAsAxiom(int formNumber) {
		Literal[] lits = new Literal[subformulas.size()];
		int i = 0;
		for (FlatFormula l: subformulas) {
			Literal lit = lits[i++] = l.getLiteral(formNumber);
			lit.getAtom().setInstantiationVariables(l.termVariables);
		}
		converter.addClause(lits,formNumber);
	}
	
	//@Override
	public Formula getSMTFormula() {
		if (smtFormula == null) {
			smtFormula = Atom.FALSE;
			for	(FlatFormula l: subformulas)
				smtFormula = converter.dpllEngine.
					orFormula(l.getSMTFormula(), smtFormula);
		}
		return smtFormula;
	}

	//@Override
	public Literal getLiteral(int formNumber) {
		if (lit == null) {
			lit = converter.createAnonAtom(smtFormula);
		}
		lit.occursIn(formNumber);
		if (!auxAxiomsAdded)
			addAuxAxioms(formNumber);
		return lit;
	}

	//@Override
	public Set<FlatFormula> getSubFormulas() {
		return subformulas;
	}
	
	//@Override
	public String toString() {
		return "(OR " + subformulas + ")";
	}		
}