package local.stalin.logic;

public class VariableTerm extends Term {
	private static final long serialVersionUID = 3583815570225859217L;
	private TermVariable var;

	VariableTerm(TermVariable v) {
		var = v;
	}
	
	public TermVariable getVariable() {
		return var;
	}
	
	public boolean typeCheck() {
		return true;
	}
	public Sort getSort() {
		return var.getSort();
	}
	
	public String toString() {
		String ann = getStringOfAnnotations();
		String rep = "?"+var.getName(); 
		if (ann != "")
			return "("+rep+ann+")";
		else
			return rep;
	}

	@Override
	public boolean containsSubTerm(Term t) {
		return t == this;
	}
}
