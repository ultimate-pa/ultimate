package local.stalin.smt.convert;

import local.stalin.logic.Formula;
import local.stalin.logic.TermVariable;
import local.stalin.smt.dpll.Literal;
import local.stalin.smt.dpll.NamedAtom;
import local.stalin.smt.theory.cclosure.CCTrigger;

public class ForallFormula extends FlatFormula {
	Formula smtFormula;
	NamedAtom lit;
	NegForallFormula negated;
	TermVariable[] vars;
	CCTrigger[] triggers;
	FlatFormula subformula;
	boolean auxAxiomsAdded;
	
	public ForallFormula(ConvertFormula converter, Formula smtForm,
			TermVariable[] vars, CCTrigger[] trigs, FlatFormula subform) {
		super(converter);
		this.smtFormula = smtForm;
		this.negated = new NegForallFormula(this);
		this.triggers = trigs;
		this.subformula = subform;
	}
	
	public FlatFormula negate() {
		return negated;
	}
	
	public void addAuxAxioms(int formNumber) {
		/* TODO: implement, i.e. add trigger to literal */
		auxAxiomsAdded = true;
	}

	public void addAsAxiom(int formNumber) {
		/* TODO: implement, i.e. install trigger */
	}
	
	public Formula getSMTFormula() {
		/* TODO: implement or store formula */
		return smtFormula;
	}

	public Literal getLiteral(int formNumber) {
		if (lit == null) {
			lit = converter.createAnonAtom(smtFormula);
		}
		lit.occursIn(formNumber);
		if (!auxAxiomsAdded)
			addAuxAxioms(formNumber);
		return lit;
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(FORALL (");
		String sep = "";
		for (TermVariable v: vars) {
			sb.append(sep).append(v.getName());
			sep = " ";
		}
		sb.append(") ").append(subformula).append(")");
		return sb.toString();
	}		
}
