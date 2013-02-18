/**
 * 
 */
package local.stalin.smt.convert;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import local.stalin.logic.Atom;
import local.stalin.logic.Formula;
import local.stalin.logic.TermVariable;
import local.stalin.smt.dpll.Literal;

class FlatFormula {
	final ConvertFormula converter;
	Set<TermVariable> termVariables;

	public FlatFormula(ConvertFormula converter) {
		this.converter = converter;
	}
	public final boolean isTrue() {
		return this == converter.TRUE;
	}
	public final boolean isFalse() {
		return this == converter.FALSE;
	}
	public boolean isSingleton() {
		return false;
	}
	public Literal getLiteral(int formNumber) {
		throw new AssertionError("getLiteral called on TRUE/FALSE");
	}
	public FlatFormula negate() {
		if (this == converter.TRUE)
			return converter.FALSE;
		else
			return converter.TRUE;
	}
	
	public Formula getSMTFormula() {
		if (this == converter.TRUE)
			return Atom.TRUE;
		else
			return Atom.FALSE;
	}
	
	public void addAsAxiom(int formNumber) {
		/* Nothing to do for TRUE */
		if (this == converter.FALSE)
			converter.addClause(new Literal[] {},formNumber);
	}
	
	public Set<FlatFormula> getSubFormulas() {
		assert (this == converter.FALSE);
		return Collections.emptySet();
	}

	public String toString() {
		return this == converter.TRUE ? "TRUE" : "FALSE";
	}
	void addTermVariable(TermVariable tv) {
		if (termVariables == null)
			termVariables = new HashSet<TermVariable>();
		termVariables.add(tv);
	}
}