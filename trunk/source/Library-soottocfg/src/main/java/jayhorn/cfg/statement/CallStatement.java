/**
 * 
 */
package jayhorn.cfg.statement;

import java.util.List;

import jayhorn.cfg.expression.Expression;
import jayhorn.cfg.method.Method;
import soot.Unit;

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
	public CallStatement(Unit createdFrom, Method method, List<Expression> arguments, List<Expression> receiver) {
		super(createdFrom);
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

}
