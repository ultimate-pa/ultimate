/**
 * 
 */
package jayhorn.cfg;

import java.util.Set;

/**
 * @author schaef
 *
 */
public interface Node {

	public Set<Variable> getUsedVariables();
	
	public Set<Variable> getLVariables();
}
