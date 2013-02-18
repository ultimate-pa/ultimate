package local.stalin.logic;

public class LetFormula extends Formula {
	private static final long serialVersionUID = 7668621000138703533L;
	private TermVariable variable;
	private Term value;
	private Formula subformula;
	
	/**
	 * @return the variable
	 */
	public TermVariable getVariable() {
		return variable;
	}

	/**
	 * @return the value
	 */
	public Term getValue() {
		return value;
	}

	/**
	 * @return the subformula
	 */
	public Formula getSubFormula() {
		return subformula;
	}

	LetFormula(TermVariable var, Term val, Formula f) {
		this.variable = var;
		this.value = val;
		this.subformula = f;
	}
	
	public boolean typeCheck() {
		return value.typeCheck() && value.getSort() == variable.getSort() 
			&& subformula.typeCheck();
	}

	public String toString() {
		return "(let (?"+variable.getName()+" "+value+") "+
			subformula + getStringOfAnnotations()+")";
	}
}
