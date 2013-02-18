package local.stalin.logic;

public class EqualsAtom extends Atom {
	private static final long serialVersionUID = 2949233801743003049L;
	private Term[] terms;
	
	EqualsAtom(Term[] terms) {
		this.terms = terms;
	}

	public Term[] getTerms() {
		return terms;
	}

	public boolean typeCheck() {
		for (int i = 0; i < terms.length; i++) {
			if (!terms[i].typeCheck() ||
				(i > 0 && terms[i].getSort() != terms[0].getSort()))
				return false;
		}
		return true;
	}

	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("(");
		sb.append("=");
		for (Term t:terms) {
			sb.append(" ").append(t);
		}
		sb.append(getStringOfAnnotations());
		sb.append(")");
		return sb.toString();
	}
}
