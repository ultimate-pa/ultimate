/**
 * 
 */
package jayhorn.cfg.expression;

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

}
