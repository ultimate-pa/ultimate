/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class ForStatementAST extends AtsASTNode {
    /**
	 * 
	 */
	private static final long serialVersionUID = 6718298270152629150L;

	public ForStatementAST(ILocation loc, AtsASTNode initStmt, AtsASTNode condition, AtsASTNode updateStmt, AtsASTNode stmtList) {
		super(loc);
		addOutgoingNode(condition);
    	addOutgoingNode(initStmt);
    	addOutgoingNode(updateStmt);
    	addOutgoingNode(stmtList);
    }

	@Override
	public String toString() {
		return "ForStatement ";
	}
}
