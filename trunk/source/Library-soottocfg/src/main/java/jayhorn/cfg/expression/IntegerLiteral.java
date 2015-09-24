/**
 * 
 */
package jayhorn.cfg.expression;

/**
 * @author schaef
 *
 */
public class IntegerLiteral extends Expression {

	private long value;
	
	public static IntegerLiteral one() {
		return new IntegerLiteral(1);
	}

	public static IntegerLiteral zero() {
		return new IntegerLiteral(0);
	}

	
	public IntegerLiteral(int value) {
		this.value = value;
	}
	
	public IntegerLiteral(long value) {
		this.value = value;
	}
	
	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder();
		sb.append(value);
		return sb.toString();		
	}	
}
