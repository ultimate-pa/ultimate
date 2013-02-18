package local.stalin.logic;

public class PredicateAtom extends Atom {
	private static final long serialVersionUID = -325368627713012847L;
	private PredicateSymbol predicate;
	private Term[] parameters;
	
	PredicateAtom(PredicateSymbol pred, Term[] params) {
		predicate = pred;
		parameters = params;
	}
	
	public PredicateSymbol getPredicate() {
		return predicate;
	}

	public Term[] getParameters() {
		return parameters;
	}

	public boolean typeCheck() {
		if (predicate.getParameterCount() != parameters.length)
			return false;
		for(int i = 0; i < parameters.length; i++) {
			if (!parameters[i].typeCheck()
				|| parameters[i].getSort() != predicate.getParameterSort(i))
				return false;
		}
		return true;
	}

	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("(");
		sb.append(predicate.getName());
		for (Term t:parameters) {
			sb.append(" ").append(t);
		}
		sb.append(getStringOfAnnotations());
		sb.append(")");
		return sb.toString();
	}
}
