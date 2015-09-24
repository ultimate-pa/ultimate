/**
 * 
 */
package jayhorn.cfg.statement;

import jayhorn.cfg.expression.Expression;
import soot.Unit;

/**
 * @author schaef
 *
 */
public class AssignStatement extends Statement {

	private final Expression left, right; 
	/**
	 * @param createdFrom
	 */
	public AssignStatement(Unit createdFrom, Expression lhs, Expression rhs) {
		super(createdFrom);
		this.left = lhs;
		this.right = rhs;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
			sb.append(this.left);
			sb.append(" := ");
			sb.append(this.right);
		return sb.toString();
	}

}
