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
public class WhileStatementAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = -5296928252765910201L;


	public WhileStatementAST(ILocation loc, AtsASTNode condition, AtsASTNode stmtList) {
		super(loc);
		addOutgoingNode(condition);
		addOutgoingNode(stmtList);
	}

	@Override
	public String toString() {
		return "WhileStatement";
	}

	@Override
	public String getAsString() {
		StringBuilder builder = new StringBuilder("while(");
		if (m_children.size() == 2) {
			builder.append(m_children.get(0).getAsString() + ") {\n");
			builder.append(m_children.get(1).getAsString());
		}
		builder.append("}");
		return builder.toString();
	}
	
	
}
