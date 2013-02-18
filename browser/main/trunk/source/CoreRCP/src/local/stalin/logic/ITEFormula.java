package local.stalin.logic;

/**
 * Represents an ite-term  (If-Then-Else).  It consists of a formula
 * and two sub terms.  One term gives the meaning for the case where
 * the formula is true, the other for the case where the formula is false.  
 * @author hoenicke
 *
 */
public class ITEFormula extends Formula {
	private static final long serialVersionUID = -3330476208341011533L;
	private Formula condition;
	private Formula trueCase;
	private Formula falseCase;
	
	ITEFormula(Formula cond, Formula trueCase, Formula falseCase) {
		this.condition = cond;
		this.trueCase = trueCase;
		this.falseCase = falseCase;
	}
	
	/**
	 * @return the condition in the If-Then-Else term.
	 */
	public Formula getCondition() {
		return condition;
	}
	
	/**
	 * @return the sub-formula for the true case.
	 */
	public Formula getTrueCase() {
		return trueCase;
	}
	/**
	 * @return the sub-formula for the false case.
	 */
	public Formula getFalseCase() {
		return falseCase;
	}

	public boolean typeCheck() {
		return trueCase.typeCheck() && falseCase.typeCheck();
	}

	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("(");
		sb.append("if_then_else");
		sb.append(" ").append(condition);
		sb.append(" ").append(trueCase);
		sb.append(" ").append(falseCase);
		sb.append(getStringOfAnnotations());
		sb.append(")");
		return sb.toString();
	}
}
