/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AtsASTNode;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class StatementList extends AtsASTNode {

	/**
	 * 
	 */
	private static final long serialVersionUID = 4839521364713345580L;

	public Class<?> getReturnType() {
		throw new RuntimeException("StatementList does not have and does not need any type!");
	}

	@Override
	public Class<?> getExpectingType() {
		throw new RuntimeException("StatementList does not have and does not need any type!");
	}

	@Override
	public String toString() {
		return "StatementList [#Statements: " + getOutgoingNodes().size() + "]";
	}

	@Override
	public String getAsString() {
		StringBuilder builder = new StringBuilder();
		for (AtsASTNode n : m_children) {
			builder.append(n.getAsString() + ";\n");
		}
		return builder.toString();
	}
	
	
}
