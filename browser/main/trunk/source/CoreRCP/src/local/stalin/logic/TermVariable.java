package local.stalin.logic;

import java.io.Serializable;

public class TermVariable implements Serializable {
	private static final long serialVersionUID = 9061998911747925090L;
	private String name;
	private Sort sort;
	
	private VariableTerm term;
	
	TermVariable(String n, Sort s) {
		name = n;
		sort = s;
	}
	
	VariableTerm createTerm() {
		if (term == null)
			term = new VariableTerm(this);
		return term;
	}
	
	public String getName() {
		return name;
	}

	public Sort getSort() {
		return sort;
	}
	
	public String toString() {
		return "(?"+name+" "+sort+")";
	}
}
