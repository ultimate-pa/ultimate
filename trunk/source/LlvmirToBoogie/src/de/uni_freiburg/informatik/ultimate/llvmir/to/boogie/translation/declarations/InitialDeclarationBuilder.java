/*
 * Copyright (C) 2025 Peter Ritter
 *
 * This file is part of the ULTIMATE LlvmirToBoogie plug-in.
 * It is used to monitor the parsing of LLVM IR files and to translate them into a Boogie AST.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LlvmirToBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LlvmirToBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LlvmirToBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LlvmirToBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations;

import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.ProcedureDeclarationBuilder.constructInitialProcedure;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.ProcedureDeclarationBuilder.constructSpecFromIdentifier;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.declarations.VariableDeclarationBuilder.constructVarDecFromString;
import static de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation.util.BoogieExpressionHelper.unifyIdentifier;

import java.util.ArrayList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LlvmirLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Builders for the initial declarations of the Boogie program.
 *
 * All methods only work on their parameters and do not access any state of the translation.
 */
public final class InitialDeclarationBuilder {

	private InitialDeclarationBuilder() {
		// utility class, not meant to be instantiated
	}

	/**
	 * Constructs initial declarations for global variables and the ULTIMATE.start procedure.
	 *
	 * This method initializes the global variables and constructs the ULTIMATE.start procedure that will be executed at
	 * the start of the program. It also constructs an aux#init procedure for global variable initialization.
	 *
	 * Using addFirst ensures that the initial declarations are at the beginning of the Boogie AST unit.
	 *
	 * @param declarations
	 *            The declarations of the Boogie AST unit, to which the initial declarations are added.
	 * @param globalVars
	 *            The global variables with their declaration and their initialization statement.
	 * @param location
	 *            The location in the source code that is used for the constructed declarations.
	 * @param logger
	 *            The logger to which errors are reported.
	 * @throws IllegalStateException
	 *             if no #main procedure is found in the declarations.
	 */
	public static void constructInitialDeclarations(final ArrayList<Declaration> declarations,
			final Map<String, Pair<Declaration, Statement>> globalVars, final LlvmirLocation location,
			final ILogger logger) throws IllegalStateException {
		final ArrayList<Statement> stmts = new ArrayList<>();
		final ArrayList<Specification> specs = new ArrayList<>();
		final ArrayList<Declaration> decls = new ArrayList<>();
		for (final String key : globalVars.keySet()) {
			final Pair<Declaration, Statement> pair = globalVars.get(key);
			if (pair == null) {
				logger.error("No pair found for global variable: " + key);
				continue;
			}
			decls.add(pair.getFirst());
			stmts.add(pair.getSecond());
			specs.add(constructSpecFromIdentifier(unifyIdentifier(key), (LlvmirLocation) pair.getSecond().getLoc()));
		}

		final String initIdentifier = "aux#init";
		declarations.addFirst(constructInitialProcedure(location, initIdentifier, new VariableDeclaration[] {},
				stmts.toArray(Statement[]::new), specs.toArray(Specification[]::new)));
		final CallStatement initCall =
				new CallStatement(location, false, new VariableLHS[] {}, initIdentifier, new Expression[] {});

		VariableLHS[] lhsVars;
		VariableDeclaration[] varDecls;
		final String mainReturnType = getMainReturnType(declarations);
		if (mainReturnType.equals("void")) {
			lhsVars = new VariableLHS[] {};
			varDecls = new VariableDeclaration[] {};
		} else {
			final String tmpVarIdentifier = "aux#tmp";
			final VariableLHS varLhs = new VariableLHS(location, tmpVarIdentifier);
			lhsVars = new VariableLHS[] { varLhs };
			varDecls =
					new VariableDeclaration[] { constructVarDecFromString(mainReturnType, tmpVarIdentifier, location) };
		}
		final CallStatement mainCall = new CallStatement(location, false, lhsVars, "#main", new Expression[] {});

		declarations.addFirst(constructInitialProcedure(location, "ULTIMATE.start", varDecls,
				new Statement[] { initCall, mainCall }, specs.toArray(Specification[]::new)));

		declarations.addAll(0, decls);
	}

	/**
	 * Retrieves the return type of the #main procedure.
	 *
	 * This method searches for the #main procedure in the given declarations and returns its return type as a String.
	 * If no such procedure is found, it throws an IllegalStateException.
	 *
	 * @param declarations
	 *            The declarations to search.
	 * @return The return type of the #main procedure.
	 * @throws IllegalStateException
	 *             if no #main procedure is found in the declarations.
	 */
	private static String getMainReturnType(final ArrayList<Declaration> declarations) throws IllegalStateException {
		final Procedure main = (Procedure) declarations.stream()
				.filter(decl -> decl instanceof Procedure && ((Procedure) decl).getIdentifier().equals("#main"))
				.findFirst().orElseThrow(() -> new IllegalStateException("No #main declaration found"));
		final String retString = main.getOutParams().length > 0 ? main.getOutParams()[0].getType().toString() : "void";
		return retString.contains("int") ? "int" : retString.contains("bool") ? "bool" : "void";
	}
}