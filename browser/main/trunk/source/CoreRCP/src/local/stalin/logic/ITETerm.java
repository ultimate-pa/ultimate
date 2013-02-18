package local.stalin.logic;

/**
 * Represents an ite-term  (If-Then-Else).  It consists of a formula
 * and two sub terms.  One term gives the meaning for the case where
 * the formula is true, the other for the case where the formula is false.  
 * @author hoenicke
 *
 */
public class ITETerm extends Term {
	private static final long serialVersionUID = -7898363109539546674L;
	private Formula condition;
	private Term trueCase;
	private Term falseCase;
	private Sort sort;
	
	public ITETerm(Formula cond, Term trueCase, Term falseCase) {
		this.condition = cond;
		this.trueCase = trueCase;
		this.falseCase = falseCase;
		sort = trueCase.getSort();
	}
	
	/**
	 * @return the condition in the If-Then-Else term.
	 */
	public Formula getCondition() {
		return condition;
	}
	
	/**
	 * @return the sub-term for the true case.
	 */
	public Term getTrueCase() {
		return trueCase;
	}
	/**
	 * @return the sub-term for the false case.
	 */
	public Term getFalseCase() {
		return falseCase;
	}

	public boolean typeCheck() {
		return trueCase.typeCheck() && falseCase.typeCheck()
			&& sort == falseCase.getSort(); 
	}

	public Sort getSort() {
		return trueCase.getSort();
	}
	
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("(");
		sb.append("ite");
		sb.append(" ").append(condition);
		sb.append(" ").append(trueCase);
		sb.append(" ").append(falseCase);
		sb.append(getStringOfAnnotations());
		sb.append(")");
		return sb.toString();
	}

	@Override
	public boolean containsSubTerm(Term t) {
		if( t == this )
			return true;
		// TODO: Should we also check condition?
		return trueCase.containsSubTerm(t) || falseCase.containsSubTerm(t);
	}
}
