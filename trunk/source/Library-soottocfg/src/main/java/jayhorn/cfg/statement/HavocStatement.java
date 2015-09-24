/**
 * 
 */
package jayhorn.cfg.statement;

import java.util.LinkedList;
import java.util.List;

import jayhorn.cfg.Variable;
import soot.Unit;

/**
 * @author schaef
 *
 */
public class HavocStatement extends Statement {

	private final List<Variable> targets;
	
	/**
	 * @param createdFrom
	 */
	public HavocStatement(Unit createdFrom, List<Variable> targets) {
		super(createdFrom);
		this.targets = new LinkedList<Variable>(targets);
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
			sb.append("havoc");
			String prefix = " ";
			for (Variable v : this.targets) {
				sb.append(prefix);
				sb.append(v);
				prefix = ", ";
			}
		return sb.toString();
	}
}
