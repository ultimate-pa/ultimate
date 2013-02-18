/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class WhileStatement extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -5296928252765910201L;


	public WhileStatement(AtsASTNode condition, AtsASTNode stmtList) {
		addOutgoingNode(condition);
		addOutgoingNode(stmtList);
	}

	@Override
	public String toString() {
		return "WhileStatement";
	}
}
