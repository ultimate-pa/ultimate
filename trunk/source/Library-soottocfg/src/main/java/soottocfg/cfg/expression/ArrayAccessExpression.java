/**
 * 
 */
package soottocfg.cfg.expression;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import soottocfg.cfg.Variable;
import soottocfg.cfg.type.Type;

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

	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		used.addAll(base.getUsedVariables());
		for (Expression e : indices) {
			used.addAll(e.getUsedVariables());
		}
		return used;
	}
	
	@Override
	public Set<Variable> getLVariables() {
		//because this can't happen on the left.
		Set<Variable> used = new HashSet<Variable>();
		return used;
	}


	@Override
	public Type getType() {
		// TODO Auto-generated method stub
		return null;
	}
	
}
