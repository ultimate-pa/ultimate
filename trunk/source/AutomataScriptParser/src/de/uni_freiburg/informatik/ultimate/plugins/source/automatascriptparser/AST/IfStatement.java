/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class IfStatement extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -4479791837394249760L;
	
	public IfStatement() {
		
	}
	
	public IfStatement(AtsASTNode condition, AtsASTNode thenStmts) {
		addOutgoingNode(condition);
		addOutgoingNode(thenStmts);
	}

	@Override
	public String toString() {
		return "IfStatement ";
	}
}
