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

package de.uni_freiburg.informatik.ultimate.llvmir.to.boogie.translation;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.DefaultLocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRBaseListener;
import de.uni_freiburg.informatik.ultimate.lib.llvmir.LLVMIRParser;

public class LlvmirToBoogieListener extends LLVMIRBaseListener {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private Unit mResult;

	// Temporary storage for function-local variables and statements
	private final ArrayList<VariableDeclaration> mFuncLocalVars = new ArrayList<>();
	private final ArrayList<Statement> mFuncBlock = new ArrayList<>();
	// Storage for the declarations that will be part of the final Boogie Unit
	private final ArrayList<Declaration> mDeclarations = new ArrayList<>();

	public LlvmirToBoogieListener(final IUltimateServiceProvider services, final ILogger logger) {
		assert services != null;
		mServices = services;
		mLogger = logger;
	}

	public Unit getResult() {
		return mResult;
	}

	/**
	 * Handles the exit event for the compilation unit in the LLVM IR parse tree.
	 *
	 * This method creates the initial procedures required for the Boogie translation, specifically an `#init` procedure
	 * and a `ULTIMATE.start` procedure that calls `#init`. These procedures are added to the list of declarations, and
	 * the resulting Boogie `Unit` is constructed and stored.
	 *
	 * @param ctx The parse tree context for the compilation unit.
	 */
	@Override
	public void exitCompilationUnit(final LLVMIRParser.CompilationUnitContext ctx) {
		final Body initBody = new Body(new DefaultLocation(), new VariableDeclaration[] {}, new Statement[] {});
		final Procedure initProcedure = new Procedure(new DefaultLocation(), new Attribute[] {}, "#init",
				new String[] {}, new VarList[] {}, new VarList[] {}, new Specification[] {}, initBody);
		mDeclarations.add(initProcedure);
		final CallStatement initCall = new CallStatement(new DefaultLocation(), false, new VariableLHS[] {}, "#init",
				new Expression[] {});
		final Body startBody = new Body(new DefaultLocation(), new VariableDeclaration[] {},
				new Statement[] { initCall });
		final Procedure startProcedure = new Procedure(new DefaultLocation(), new Attribute[] {}, "ULTIMATE.start",
				new String[] {}, new VarList[] {}, new VarList[] {}, new Specification[] {}, startBody);
		mDeclarations.add(startProcedure);

		mResult = new Unit(new DefaultLocation(), mDeclarations.toArray(Declaration[]::new));
	}

	/**
	 * Handles the exit event for a function definition in the LLVM IR parse tree.
	 *
	 * This method translates the parsed LLVM IR function into a Boogie procedure, including its body, parameters, and
	 * return type. Currently, only `void` and integer return types are supported. If the return type is not supported,
	 * a fatal log message is issued.
	 *
	 * @param ctx The parse tree context for the function definition.
	 */

	@Override
	public void exitFuncDef(final LLVMIRParser.FuncDefContext ctx) {
		final String funcName = unifyFuncName(ctx.funcHeader().GlobalIdent().getText());
		final LLVMIRParser.TypeContext returnType = ctx.funcHeader().type();
		final Body funcBody = new Body(new DefaultLocation(), mFuncLocalVars.toArray(VariableDeclaration[]::new),
				mFuncBlock.toArray(Statement[]::new));
		final ArrayList<Attribute> attributes = new ArrayList<>();
		final ArrayList<String> typeParams = new ArrayList<>();
		final ArrayList<VarList> inParams = new ArrayList<>();
		final ArrayList<VarList> outParams = new ArrayList<>();
		final ArrayList<Specification> spec = new ArrayList<>();

		if (returnType.getText().equals("void")) {
			// Nothing gets returned
		} else if (returnType.intType() != null) {
			final PrimitiveType intType = new PrimitiveType(new DefaultLocation(), "int");
			final VarList retVarList = new VarList(new DefaultLocation(), new String[] { "ret" }, intType);
			outParams.add(retVarList);
		} else {
			mLogger.fatal("The support for return types other than void and integers is not implemented yet.");
		}

		final Procedure procedure = new Procedure(new DefaultLocation(), attributes.toArray(Attribute[]::new), funcName,
				typeParams.toArray(String[]::new), inParams.toArray(VarList[]::new), outParams.toArray(VarList[]::new),
				spec.toArray(Specification[]::new), funcBody);
		mDeclarations.add(procedure);

		mFuncBlock.clear();
		mFuncLocalVars.clear();
	}

	/**
	 * FuncNames in LLVM IR begin with '@', but in Boogie we want them to begin with '#'.
	 *
	 * @param funcName the name of the function as it appears in LLVM IR
	 * @return the unified function name for Boogie, with '@' replaced by '#'
	 */
	private String unifyFuncName(final String funcName) {
		return funcName.replace('@', '#');
	}

	/**
	 * Handles the exit event for a return terminator in the LLVM IR parse tree.
	 *
	 * Currently, it only supports integer return types. If the return type is not supported, a fatal log message is
	 * issued.
	 *
	 * @param ctx The parse tree context for the return terminator.
	 */
	@Override
	public void exitRetTerm(final LLVMIRParser.RetTermContext ctx) {
		final LLVMIRParser.ConcreteTypeContext returnType = ctx.concreteType();
		if (returnType.intType() != null) {
			final String returnValue = ctx.value().constant().intConst().getText();
			final IntegerLiteral returnLiteral = new IntegerLiteral(new DefaultLocation(), returnValue);
			final VariableLHS returnVar = new VariableLHS(new DefaultLocation(), "ret");
			final AssignmentStatement assignmentStmt = new AssignmentStatement(new DefaultLocation(),
					new LeftHandSide[] { returnVar }, new Expression[] { returnLiteral });
			final ReturnStatement returnStmt = new ReturnStatement(new DefaultLocation());
			mFuncBlock.add(assignmentStmt);
			mFuncBlock.add(returnStmt);
		} else {
			mLogger.fatal("The support for return types other than integers is not implemented yet.");
		}
	}
}
