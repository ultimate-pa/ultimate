/**
 * 
 */
package jayhorn.cfg.expression;

import jayhorn.cfg.Variable;

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
		sb.append(this.variable.getName());
		return sb.toString();		
	}	
}
