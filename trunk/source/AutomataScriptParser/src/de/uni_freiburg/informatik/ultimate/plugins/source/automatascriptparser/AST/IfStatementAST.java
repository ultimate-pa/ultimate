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
public class IfStatementAST extends AtsASTNode {
	
	/**
	 * 
	 */
	private static final long serialVersionUID = -4479791837394249760L;
	
	public IfStatementAST(ILocation loc) {
		super(loc);
	}
	
	public IfStatementAST(ILocation loc, AtsASTNode condition, AtsASTNode thenStmts) {
		super(loc);
		addOutgoingNode(condition);
		addOutgoingNode(thenStmts);
	}

	@Override
	public String toString() {
		return "IfStatement ";
	}

	@Override
	public String getAsString() {
		if (m_children.size() == 2) {
			StringBuilder builder = new StringBuilder("if (");
			builder.append(m_children.get(0).getAsString());
			builder.append(") {\n");
			builder.append(m_children.get(1).getAsString());
			builder.append("\n}\n");
			return builder.toString();
		} else {
			return "";
		}
	}
	
	
}
