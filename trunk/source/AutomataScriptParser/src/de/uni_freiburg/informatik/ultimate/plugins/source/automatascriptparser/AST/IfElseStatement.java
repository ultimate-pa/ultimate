/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class IfElseStatement extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 7360382688960711445L;

	public IfElseStatement(AtsASTNode condition, AtsASTNode thenStmts, AtsASTNode elseStmts) {
		addOutgoingNode(condition);
		addOutgoingNode(thenStmts);
		addOutgoingNode(elseStmts);
	}

	@Override
	public String toString() {
		return "IfElseStatement";
	}
}
