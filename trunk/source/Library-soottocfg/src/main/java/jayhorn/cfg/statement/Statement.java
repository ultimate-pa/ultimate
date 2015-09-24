/**
 * 
 */
package jayhorn.cfg.statement;

import jayhorn.cfg.Node;
import jayhorn.soot.util.SootTranslationHelpers;
import soot.Unit;

/**
 * @author schaef
 *
 */
public abstract class Statement implements Node {

	private final int javaSourceLineNumber;

	public Statement(Unit createdFrom) {

		int lineNumber = createdFrom.getJavaSourceStartLineNumber();

		if (lineNumber < 0) {
			lineNumber = SootTranslationHelpers.v().getJavaSourceLine(
					SootTranslationHelpers.v().getCurrentMethod());
		}

		this.javaSourceLineNumber = lineNumber;
	}

	public int getJavaSourceLine() {
		return this.javaSourceLineNumber;
	}
}
