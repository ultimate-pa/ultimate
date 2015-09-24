/**
 * 
 */
package jayhorn.cfg.expression;


/**
 * @author schaef
 *
 */
public class BinaryExpression extends Expression {

	public enum BinaryOperator {
		Plus("+"), Minus("-"), Mul("*"), Div("/"), Mod("%"),
		And("&&"), Or("||"), Xor("^"), Implies("->"),
		Eq("=="), Ne("!="), Gt(">"), Ge(">="), Lt("<"), Le("<="),
		Shl("<<"), Shr(">>"), Ushr("u>>"), BOr("|"), BAnd("&");
		
		private final String name;       

	    private BinaryOperator(String s) {
	        name = s;
	    }

	    public boolean equalsName(String otherName) {
	        return (otherName == null) ? false : name.equals(otherName);
	    }

	    public String toString() {
	       return this.name;
	    }		
	}
	
	private final Expression left, right;
	private final BinaryOperator op;
	
	public BinaryExpression(BinaryOperator op, Expression left, Expression right) {
		this.left = left;
		this.right = right;
		this.op = op;
	}
	
	public Expression getLeft() {
		return left;
	}

	public Expression getRight() {
		return right;
	}

	public BinaryOperator getOp() {
		return op;
	}

	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(this.left);
		sb.append(" "+this.op+" ");
		sb.append(this.right);
		sb.append(")");
		return sb.toString();		
	}
	
}
