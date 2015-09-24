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
public class ArrayStoreExpression extends Expression {

	private final Expression base, value;
	private final List<Expression> indices;

	/**
	 * 
	 */
	public ArrayStoreExpression(Expression base, Expression[] indices,
			Expression value) {
		this.base = base;
		this.indices = new LinkedList<Expression>();
		for (int i = 0; i < indices.length; i++) {
			this.indices.add(indices[i]);
		}
		this.value = value;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("store(");
		sb.append(this.base);
		sb.append(",");
		String comma = "";
		for (Expression e : this.indices) {
			sb.append(comma);
			sb.append(e);
			comma = ", ";
		}
		sb.append(",");
		sb.append(this.value);
		sb.append(")");
		return sb.toString();
	}

}
