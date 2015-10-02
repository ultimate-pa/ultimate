/**
 * 
 */
package soottocfg.cfg.expression;

import java.util.HashSet;
import java.util.Set;

import soottocfg.cfg.Variable;
import soottocfg.cfg.type.BoolType;
import soottocfg.cfg.type.Type;

/**
 * @author schaef
 *
 */
public class BooleanLiteral extends Expression {

	private boolean value;

	public static BooleanLiteral trueLiteral() {
		return new BooleanLiteral(true);
	}

	public static BooleanLiteral falseLiteral() {
		return new BooleanLiteral(false);
	}

	public BooleanLiteral(boolean value) {
		this.value = value;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(value);
		return sb.toString();
	}
	
	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		return used;
	}

	@Override
	public Set<Variable> getLVariables() {
		Set<Variable> used = new HashSet<Variable>();
		return used;
	}

	@Override
	public Type getType() {
		return BoolType.instance();
	}

}
