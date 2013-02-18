package local.stalin.logic;

public class VariableAtom extends Atom {
	private static final long serialVersionUID = 8159820672566590890L;
	private FormulaVariable var;
	
	VariableAtom(FormulaVariable var) {
		this.var = var;
	}
	
	public FormulaVariable getVariable() {
		return var;
	}
	
	public boolean typeCheck() {
		return true;
	}

	public String toString() {
		String ann = getStringOfAnnotations();
		String rep = "$"+var.getName(); 
		if (ann != "")
			return "("+rep+ann+")";
		else
			return rep;
	}
}
