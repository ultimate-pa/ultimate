/**
 * 
 */
package jayhorn.cfg.expression;

import jayhorn.cfg.Variable;

/**
 * @author schaef
 *
 */
public class InstanceOfExpression extends Expression {

	private final Expression expression;
	private final Variable typeVariable;
	
	/**
	 * 
	 */
	public InstanceOfExpression(Expression expr, Variable typeVar) {
		this.expression = expr;
		this.typeVariable = typeVar;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(this.expression);
		sb.append(" instanceof ");
		sb.append(this.typeVariable.getName());
		sb.append(")");
		return sb.toString();
	}
}
