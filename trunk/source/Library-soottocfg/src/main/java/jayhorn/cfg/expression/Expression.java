/**
 * 
 */
package jayhorn.cfg.expression;

import java.util.Set;

import jayhorn.cfg.Node;
import jayhorn.cfg.Variable;
import jayhorn.cfg.type.Type;

/**
 * @author schaef
 *
 */
public abstract class Expression implements Node {

	public abstract Set<Variable> getUsedVariables();
	
	public abstract Set<Variable> getLVariables();
	
	public abstract Type getType();
		
}
