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
