/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2026 École Polytechnique
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

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.function.BiConsumer;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Axiom;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IToString;

/**
 * Provides static methods to get a pretty-printed String representation of Boogie AST nodes.
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 * @author Dominik Klumpp (klumpp@lix.polytechnique.fr)
 *
 */
public final class BoogiePrettyPrinter {
	private static final String LINEBREAK = System.getProperty("line.separator");
	private static final IToString<BoogieASTNode> BOOGIE_STRING_PROVIDER = new BoogieStringProvider();

	private BoogiePrettyPrinter() {
		// utility class does not have a constructor
	}

	public static String print(final Axiom axiom) {
		return printWithoutLastLinebreak(axiom, BoogieOutput::printAxiom);
	}

	public static String print(final Statement stmt) {
		return printWithoutLastLinebreak(stmt, BoogieOutput::printStatement);
	}

	public static String print(final Expression expr) {
		return printWithoutLastLinebreak(expr, BoogieOutput::printExpression);
	}

	public static String print(final Specification spec) {
		return printWithoutLastLinebreak(spec, BoogieOutput::printSpecification);
	}

	public static String print(final VariableDeclaration decl) {
		return printWithoutLastLinebreak(decl, BoogieOutput::printVariableDeclaration);
	}

	public static String print(final VarList... decl) {
		return printWithoutLastLinebreak(decl, BoogieOutput::printVarList);
	}

	public static String print(final VarList decl) {
		return printWithoutLastLinebreak(decl, BoogieOutput::printVarList);
	}

	public static String printSignature(final Procedure decl) {
		final Procedure actual = new Procedure(decl.getLocation(), decl.getAttributes(), decl.getIdentifier(),
				decl.getTypeParams(), decl.getInParams(), decl.getOutParams(), decl.getSpecification(), null);
		return printWithoutLastLinebreak(actual, BoogieOutput::printProcedure);
	}

	public static String print(final ASTType astType) {
		return printWithoutLastLinebreak(astType, BoogieOutput::printType);
	}

	public static String print(final Attribute[] attrs) {
		return printToString(attrs, BoogieOutput::printAttributes);
	}

	public static IToString<BoogieASTNode> getBoogieToStringProvider() {
		return BOOGIE_STRING_PROVIDER;
	}

	private static <T> String printToString(final T elem, final BiConsumer<BoogieOutput, T> printer) {
		final StringWriter strWriter = new StringWriter();
		try (var output = new BoogieOutput(new PrintWriter(strWriter))) {
			printer.accept(output, elem);
		}
		return strWriter.toString();
	}

	private static <T> String printWithoutLastLinebreak(final T elem, final BiConsumer<BoogieOutput, T> printer) {
		return removeLastLinebreak(printToString(elem, printer));
	}

	private static String removeLastLinebreak(final String str) {
		final int length = str.length();
		final int linebreakLength = LINEBREAK.length();
		if (length >= linebreakLength && str.substring(length - linebreakLength, length).equals(LINEBREAK)) {
			return str.substring(0, length - linebreakLength);
		}
		return str;
	}

	private static final class BoogieStringProvider implements IToString<BoogieASTNode> {
		@Override
		public String toString(final BoogieASTNode elem) {
			return switch (elem) {
			case final Expression expr -> print(expr);
			case final Statement stmt -> print(stmt);
			case final VarList vlist -> print(vlist);
			case final VariableDeclaration decl -> print(decl);
			case final Specification spec -> print(spec);
			default -> elem.toString();
			};
		}
	}
}
