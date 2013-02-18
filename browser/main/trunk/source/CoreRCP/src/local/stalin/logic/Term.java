package local.stalin.logic;

public abstract class Term extends SMTLibBase {	
	private static final long serialVersionUID = 2247757695666105108L;
	protected Term() {
	}

	public abstract Sort getSort();
	public abstract boolean containsSubTerm(Term t);
}
