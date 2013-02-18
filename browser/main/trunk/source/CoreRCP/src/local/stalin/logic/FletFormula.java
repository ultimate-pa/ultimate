package local.stalin.logic;

public class FletFormula extends Formula {
	private static final long serialVersionUID = -5846955187964578230L;
	private FormulaVariable variable;
	private Formula value;
	private Formula subformula;
	
	FletFormula(FormulaVariable var, Formula val, Formula f) {
		this.variable = var;
		this.value = val;
		this.subformula = f;
	}
	
	public FormulaVariable getVariable() {
		return variable;
	}
	public Formula getValue() {
		return value;
	}
	public Formula getSubFormula() {
		return subformula;
	}

	public boolean typeCheck() {
		return value.typeCheck() && subformula.typeCheck();
	}

	public String toString() {
		return "(flet ($"+variable.getName()+" "+value+") "+
			subformula + getStringOfAnnotations()+")";
	}
}
