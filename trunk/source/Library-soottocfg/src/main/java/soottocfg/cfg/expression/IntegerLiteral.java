/**
 * 
 */
package soottocfg.cfg.expression;

import java.util.HashSet;
import java.util.Set;

import soottocfg.cfg.Variable;
import soottocfg.cfg.type.IntType;
import soottocfg.cfg.type.Type;

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
	
	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
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
		return IntType.instance();
	}
}
