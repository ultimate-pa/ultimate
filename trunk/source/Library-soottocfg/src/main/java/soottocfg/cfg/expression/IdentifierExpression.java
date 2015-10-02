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
public class IdentifierExpression extends Expression {

	private Variable variable;
	
	/**
	 * 
	 */
	public IdentifierExpression(Variable v) {
		this.variable = v;
	}

	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder();
		if (this.variable==null) {
			sb.append("==NOT IMPLEMENTED==");
		} else {
			sb.append(this.variable.getName());
		}
		return sb.toString();		
	}	
	
	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		used.add(variable);
		return used;
	}
	
	@Override
	public Set<Variable> getLVariables() {
		return getUsedVariables();
	}

	
	@Override
	public Type getType() {
		return variable.getType();
	}
}
