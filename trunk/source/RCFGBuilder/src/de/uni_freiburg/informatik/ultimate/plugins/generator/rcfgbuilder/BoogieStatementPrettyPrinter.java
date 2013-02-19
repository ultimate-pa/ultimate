package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.io.PrintWriter;
import java.io.StringWriter;

import de.uni_freiburg.informatik.ultimate.boogie.printer.BoogieOutput;
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
		StringWriter wr = new StringWriter();
		PrintWriter pw = new PrintWriter(wr);
		BoogieOutput output = new BoogieOutput(pw);
		output.printStatement(st, "");
		pw.close();
		return wr.getBuffer().toString();
	}
	
	/**
	 * @return prettyprinted Expression
	 */
	public static String print(Expression expr) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.printExpression(sb, expr);
		return sb.toString();
	}
}
