/**
 * 
 */
package jayhorn.cfg.expression;

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
	
}
