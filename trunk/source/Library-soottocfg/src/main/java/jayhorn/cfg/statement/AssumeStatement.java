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
public class AssumeStatement extends Statement {

	private final Expression expression;
	
	/**
	 * @param createdFrom
	 */
	public AssumeStatement(Unit createdFrom, Expression expr) {
		super(createdFrom);
		this.expression = expr; 
	}

	public Expression getExpression() {
		return this.expression;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
			sb.append("assume ");
			sb.append(this.expression);
		return sb.toString();
	}
}
