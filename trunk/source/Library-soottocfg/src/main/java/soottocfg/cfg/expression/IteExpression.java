/**
 * 
 */
package soottocfg.cfg.expression;

import java.util.HashSet;
import java.util.Set;

import soottocfg.cfg.Variable;
import soottocfg.cfg.type.Type;

/**
 * @author schaef
 *
 */
public class IteExpression extends Expression {

	private final Expression condition, thenExpr, elseExpr;
	
	public IteExpression(Expression condition, Expression thenExpr, Expression elseExpr) {
		this.condition = condition;
		this.thenExpr = thenExpr;
		this.elseExpr = elseExpr;
	}
	
	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(this.condition);
		sb.append("?");
		sb.append(this.thenExpr);
		sb.append(":");
		sb.append(this.elseExpr);
		sb.append(")");
		return sb.toString();		
	}	

	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		used.addAll(condition.getUsedVariables());
		used.addAll(thenExpr.getUsedVariables());
		used.addAll(elseExpr.getUsedVariables());
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
		assert (thenExpr.getType().equals(elseExpr.getType()));
		return thenExpr.getType();
	}
	
}
