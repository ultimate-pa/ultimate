/**
 * 
 */
package jayhorn.cfg.expression;

import java.util.HashSet;
import java.util.Set;

import jayhorn.cfg.Variable;
import jayhorn.cfg.type.BoolType;
import jayhorn.cfg.type.Type;

/**
 * @author schaef
 *
 */
public class UnaryExpression extends Expression {

	public enum UnaryOperator {
		Neg("-"), LNot("!");
		private final String name;       

	    private UnaryOperator(String s) {
	        name = s;
	    }

	    public boolean equalsName(String otherName) {
	        return (otherName == null) ? false : name.equals(otherName);
	    }

	    @Override
		public String toString() {
	       return this.name;
	    }			
	}
	
	private final Expression expression;
	private final UnaryOperator op;
	
	public UnaryExpression(UnaryOperator op, Expression inner) {
		this.expression = inner;
		this.op = op;
	}
	
	public Expression getExpression() {
		return expression;
	}

	public UnaryOperator getOp() {
		return op;
	}

	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(this.op);
		sb.append(this.expression);
		sb.append(")");
		return sb.toString();		
	}

	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		used.addAll(expression.getUsedVariables());
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
		switch (op) {
		case LNot: {
			return BoolType.instance();
		}
		case Neg: {
			return expression.getType();
		}
		}
		throw new RuntimeException("Unknown case " + op);
	}

}
