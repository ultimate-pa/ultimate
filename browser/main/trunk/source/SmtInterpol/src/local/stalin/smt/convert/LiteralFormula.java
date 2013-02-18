/**
 * 
 */
package local.stalin.smt.convert;

import java.util.Collections;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.logic.TermVariable;
import local.stalin.smt.dpll.Literal;

class LiteralFormula extends FlatFormula {
	final Literal lit;
	Formula smtFormula;
	LiteralFormula negated;

	public LiteralFormula(ConvertFormula converter, Formula smtFormula, Literal lit) {
		super(converter);
		this.smtFormula = smtFormula;
		this.lit = lit;
	}
	public FlatFormula negate() {
		if (negated == null) {
			negated = converter.createLiteralFormula(null, lit.negate());
			negated.negated = this;
//			negated.termVariables = termVariables;
		}
		negated.termVariables = termVariables;
		return negated;
	}
	//@Override
	public Formula getSMTFormula() {
		if (smtFormula == null)
			smtFormula = lit.getSMTFormula(converter.dpllEngine.getSMTTheory());
		return smtFormula;
	}
	//@Override
	public Literal getLiteral(int formNumber) {
		return lit;
	}
	//@Override
	public String toString() {
		return lit.toString();
	}

	//@Override
	public void addAsAxiom(int formNumber) {
		lit.getAtom().setInstantiationVariables(termVariables);
		converter.addClause(new Literal[] { lit },formNumber);
	}

	public Set<FlatFormula> getSubFormulas() {
		return Collections.singleton((FlatFormula) this);
	}
	@Override
	void addTermVariable(TermVariable tv) {
		super.addTermVariable(tv);
		lit.getAtom().addInstantiationVariable(tv);
	}	
}