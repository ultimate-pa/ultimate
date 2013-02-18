package local.stalin.smt.convert;

import local.stalin.logic.Formula;
import local.stalin.smt.dpll.Literal;

public class NegForallFormula extends FlatFormula {
	ForallFormula positive;
	boolean auxAxiomsAdded;
	
	public NegForallFormula(ForallFormula pos) {
		super(pos.converter);
		this.positive = pos;
	}

	public FlatFormula negate() {
		return positive;
	}
	
	public void addAuxAxioms(int formNumber) {
		/* TODO: add aux skolemized form */
		auxAxiomsAdded = true;;
	}
	
	//@Override
	public void addAsAxiom(int formNumber) {
		/* TODO: add skolemized form */
	}
	
	//@Override
	public Formula getSMTFormula() {
		return converter.dpllEngine.getSMTTheory().not(positive.getSMTFormula());
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

	//@Override
	public String toString() {
		return "(NOT "+positive+")";
	}
}
