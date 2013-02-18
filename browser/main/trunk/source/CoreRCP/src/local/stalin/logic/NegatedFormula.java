package local.stalin.logic;

public class NegatedFormula extends Formula {
	private static final long serialVersionUID = -2253562447533410159L;
	private Formula subformula;

	NegatedFormula(Formula f) {
		subformula = f;
	}
	
	public boolean typeCheck() {
		return subformula.typeCheck();
	}
	
	public String toString() {
		return "(not "+subformula+")";
	}

	/**
	 * @return the sub formula
	 */
	public Formula getSubFormula() {
		return subformula;
	}
}
