/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;
/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class IfElseStatementAST extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 7360382688960711445L;

	public IfElseStatementAST(AtsASTNode condition, AtsASTNode thenStmts, AtsASTNode elseStmts) {
		addOutgoingNode(condition);
		addOutgoingNode(thenStmts);
		addOutgoingNode(elseStmts);
	}

	@Override
	public String toString() {
		return "IfElseStatement";
	}

	@Override
	public String getAsString() {
		if (m_children.size() == 3) {
			StringBuilder builder = new StringBuilder("if (");
			builder.append(m_children.get(0).getAsString());
			builder.append(") {\n");
			builder.append(m_children.get(1).getAsString());
			builder.append("\n} else {\n");
			builder.append(m_children.get(2).getAsString());
			builder.append("\n}");
			return builder.toString();
		} else {
			return "";
		}
	}
	
	
}
