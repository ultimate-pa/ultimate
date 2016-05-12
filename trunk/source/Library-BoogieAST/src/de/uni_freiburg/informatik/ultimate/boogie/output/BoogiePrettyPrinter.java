/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.boogie.output;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.translation.IToString;

/**
 * Provides a static method to get a prettyprinted String representation of a (Boogie) Statement.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */

public class BoogiePrettyPrinter {

	private static final String sLinebreak = System.getProperty("line.separator");
	private static final IToString<BoogieASTNode> sBoogieStringProvider = new BoogieStringProvider();;

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

	public static String print(Specification spec) {
		BoogieOutput output = new BoogieOutput(null);
		StringBuilder sb = new StringBuilder();
		output.appendSpecification(sb, spec);
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

	public static IToString<BoogieASTNode> getBoogieToStringprovider() {
		return sBoogieStringProvider;
	}

	private static void removeLastLinebreak(StringBuilder sb) {
		int length = sb.length();
		int linebreakLength = sLinebreak.length();
		if (length < linebreakLength) {
			return;
		}

		if (sb.substring(length - linebreakLength, length).equals(sLinebreak)) {
			sb.replace(length - linebreakLength, length, "");
		}
	}

	private static final class BoogieStringProvider implements IToString<BoogieASTNode> {
		@Override
		public String toString(BoogieASTNode elem) {
			if (elem instanceof Expression) {
				return BoogiePrettyPrinter.print((Expression) elem);
			} else if (elem instanceof Statement) {
				return BoogiePrettyPrinter.print((Statement) elem);
			} else if (elem instanceof VarList) {
				return BoogiePrettyPrinter.print((VarList) elem);
			} else if (elem instanceof VariableDeclaration) {
				return BoogiePrettyPrinter.print((VariableDeclaration) elem);
			} else if (elem instanceof Specification) {
				return BoogiePrettyPrinter.print((Specification) elem);
			} else {
				return elem.toString();
			}
		}
	}
}
