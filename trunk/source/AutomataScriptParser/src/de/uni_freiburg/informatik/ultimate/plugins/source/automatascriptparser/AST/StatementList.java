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

	@Override
	public boolean isTypeCorrect(Class<?> expectedType) {
		throw new RuntimeException("StatementList does not have and does not need any type!");
	}

	@Override
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
}
