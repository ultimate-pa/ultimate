/**
 * 
 */
package jayhorn.cfg.statement;

import jayhorn.cfg.expression.Expression;
import soot.Unit;

/**
 * @author teme
 *
 */
public class AssertStatement extends Statement {

	private final Expression expression;
	
	/**
	 * @param createdFrom
	 */
	public AssertStatement(Unit createdFrom, Expression expr) {
		super(createdFrom);
		this.expression = expr; 
	}

	public Expression getExpression() {
		return this.expression;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
			sb.append("assert ");
			sb.append(this.expression);
		return sb.toString();
	}
}
