/**
 * 
 */
package soottocfg.cfg.statement;

import java.util.HashSet;
import java.util.Set;

import soottocfg.cfg.SourceLocation;
import soottocfg.cfg.Variable;
import soottocfg.cfg.expression.Expression;

/**
 * @author teme
 *
 */
public class AssertStatement extends Statement {

	private final Expression expression;
	
	/**
	 * @param createdFrom
	 */
	public AssertStatement(SourceLocation loc, Expression expr) {
		super(loc);
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
	
	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		used.addAll(expression.getUsedVariables());
		return used;
	}
	
	@Override
	public Set<Variable> getLVariables() {
		Set<Variable> used = new HashSet<Variable>();
		return used;
	}

}
