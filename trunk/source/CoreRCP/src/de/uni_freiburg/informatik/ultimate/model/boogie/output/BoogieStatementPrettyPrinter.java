package de.uni_freiburg.informatik.ultimate.model.boogie.output;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * Provides a static method to get a prettyprinted String representation of a
 * (Boogie) Statement.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */

public class BoogieStatementPrettyPrinter {

	private static final String sLinebreak = System.getProperty("line.separator");

	/**
	 * @return prettyprinted String representation the Statement st
	 */
	public static String print(Statement st) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendStatement(sb, st);
		removeLastLinebreak(sb);
		return sb.toString();
	}

	/**
	 * @return prettyprinted Expression
	 */
	public static String print(Expression expr) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendExpression(sb, expr);
		removeLastLinebreak(sb);
		return sb.toString();
	}

	public static String print(VariableDeclaration decl) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendVariableDeclaration(sb, decl);
		removeLastLinebreak(sb);
		return sb.toString();
	}

	public static String print(VarList[] decl) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendVarList(sb, decl);
		removeLastLinebreak(sb);
		return sb.toString();
	}

	public static String print(VarList decl) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendVarList(sb, new VarList[] { decl });
		removeLastLinebreak(sb);
		return sb.toString();
	}

	public static String printSignature(Procedure decl) {
		Procedure actual = new Procedure(decl.getLocation(), decl.getAttributes(), decl.getIdentifier(),
				decl.getTypeParams(), decl.getInParams(), decl.getOutParams(), decl.getSpecification(), null);
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendProcedure(sb, actual);
		removeLastLinebreak(sb);
		return sb.toString();
	}

	private static void removeLastLinebreak(StringBuilder sb) {
		int length = sb.length();
		int linebreakLength = sLinebreak.length();
		if(length<linebreakLength){
			return;
		}
		
		if (sb.substring(length - linebreakLength, length).equals(sLinebreak)) {
			sb.replace(length - linebreakLength, length, "");
		}
	}

}
