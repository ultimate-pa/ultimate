/**
 * 
 */
package jayhorn.cfg;

import jayhorn.cfg.type.Type;

/**
 * @author schaef
 *
 */
public class Variable implements Node {

	private final String variableName;
	
	/**
	 * 
	 */
	public Variable(String name, Type t) {
		// TODO Auto-generated constructor stub
		this.variableName = name;
	}
	
	public String getName() {
		return this.variableName;
	}

}
