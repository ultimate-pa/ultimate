/**
 * 
 */
package jayhorn.cfg.expression;

import java.util.LinkedList;
import java.util.List;

/**
 * @author schaef
 *
 */
public class ArrayAccessExpression extends Expression {

	private final Expression base;
	private final List<Expression> indices;

	/**
	 * 
	 */
	public ArrayAccessExpression(Expression base, Expression[] indices) {
		this.base = base;
		this.indices = new LinkedList<Expression>();
		for (int i = 0; i < indices.length; i++) {
			this.indices.add(indices[i]);
		}
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("load(");
		sb.append(this.base);
		sb.append(",");
		String comma = "";
		for (Expression e : this.indices) {
			sb.append(comma);
			sb.append(e);
			comma = ", ";
		}
		sb.append(")");
		return sb.toString();
	}
	
}
