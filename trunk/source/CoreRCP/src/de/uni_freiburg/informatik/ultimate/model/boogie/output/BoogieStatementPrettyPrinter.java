package de.uni_freiburg.informatik.ultimate.model.boogie.output;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

/**
 * Provides a static method to get a prettyprinted String representation of a
 * (Boogie) Statement.
 * @author heizmann@informatik.uni-freiburg.de
 *
 */

public class BoogieStatementPrettyPrinter {
	
	/**
	 * @return prettyprinted String representation the Statement st
	 */
	public static String print(Statement st) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendStatement(sb, st);
		return sb.toString();
	}
	
	/**
	 * @return prettyprinted Expression
	 */
	public static String print(Expression expr) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendExpression(sb, expr);
		return sb.toString();
	}
}
