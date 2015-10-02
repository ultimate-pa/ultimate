/**
 * 
 */
package soottocfg.cfg.expression;

import java.util.Set;

import soottocfg.cfg.Node;
import soottocfg.cfg.Variable;
import soottocfg.cfg.type.Type;

/**
 * @author schaef
 *
 */
public abstract class Expression implements Node {

	public abstract Set<Variable> getUsedVariables();
	
	public abstract Set<Variable> getLVariables();
	
	public abstract Type getType();
		
}
