/**
 * 
 */
package jayhorn.cfg.statement;

import java.util.Set;

import jayhorn.cfg.Node;
import jayhorn.cfg.SourceLocation;
import jayhorn.cfg.Variable;

/**
 * @author schaef
 *
 */
public abstract class Statement implements Node {

	private final SourceLocation sourceLocation;

	public Statement(SourceLocation loc) {
		this.sourceLocation = loc;

	}

	public abstract Set<Variable> getUsedVariables();
	
	public abstract Set<Variable> getLVariables();
	
	public int getJavaSourceLine() {
		return this.sourceLocation.getLineNumber();
	}
}
