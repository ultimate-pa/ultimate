/**
 * 
 */
package jayhorn.cfg.expression;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import jayhorn.cfg.Variable;
import jayhorn.cfg.type.Type;

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

	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		used.addAll(base.getUsedVariables());
		for (Expression e : indices) {
			used.addAll(e.getUsedVariables());
		}
		used.addAll(value.getUsedVariables());
		return used;
	}

	@Override
	public Set<Variable> getLVariables() {
		Set<Variable> used = new HashSet<Variable>();
		used.addAll(base.getLVariables());
		return used;
	}
	
	@Override
	public Type getType() {
		return base.getType();
	}

}
