/**
 * 
 */
package jayhorn.cfg.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import jayhorn.cfg.SourceLocation;
import jayhorn.cfg.Variable;
import jayhorn.cfg.expression.Expression;
import jayhorn.cfg.method.Method;

/**
 * @author schaef
 *
 */
public class CallStatement extends Statement {

	private final Method method;
	private final List<Expression> arguments; 
	private final List<Expression> receiver;
	/**
	 * @param createdFrom
	 */
	public CallStatement(SourceLocation loc, Method method, List<Expression> arguments, List<Expression> receiver) {
		super(loc);
		this.method = method;
		this.arguments = arguments;
		this.receiver = receiver;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		String comma = "";
		for (Expression e : this.receiver) {
			sb.append(comma);
			sb.append(e);
			comma = ", ";
		}
		sb.append(" := call ");
		sb.append(this.method.getMethodName());
		sb.append("(");
		comma = "";
		for (Expression e : this.arguments) {
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
		for (Expression e : arguments) {
			used.addAll(e.getUsedVariables());
		}
		for (Expression e : receiver) {
			used.addAll(e.getUsedVariables());
		}		
		return used;
	}

	@Override
	public Set<Variable> getLVariables() {
		Set<Variable> used = new HashSet<Variable>();
		for (Expression e : receiver) {
			used.addAll(e.getLVariables());
		}				
		return used;
	}
}
