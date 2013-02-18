package local.stalin.logic;

/**
 * A program variable term is the reference of a program variable inside a formula.
 * Before converting to SMT, these should be replaced by constant symbol applications.
 * @author hoenicke
 *
 */
public class ProgramVariableTerm extends Term {
	private static final long serialVersionUID = -1959955868016773490L;
	private ProgramVariable var;
	private boolean useOldValue;

	ProgramVariableTerm(ProgramVariable v, boolean old) {
		var = v;
		useOldValue = old;
	}
	ProgramVariableTerm(ProgramVariable v) {
		this(v, false);
	}
	
	public boolean typeCheck() {
		return true;
	}
	public Sort getSort() {
		return var.getSort();
	}
	
	public String toString() {
		String ann = getStringOfAnnotations();
		String rep = "V'."+var.getName();
		if (useOldValue)
			rep += "'.0";
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
