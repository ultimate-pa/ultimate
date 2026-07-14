/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Oleksii Saukh (saukho@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Stefan Wissert
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * An example for a ACSL handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.FlatSymbolTable;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.IMemoryPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.ProcedureManager;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.InterruptRequestHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptMaskingFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptPriorityFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps.function.InterruptServiceFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.InterruptResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.CdtASTUtils;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IACSLHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLProblemNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assertion;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.AtLabelExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CastExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnotStmt;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ContractStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FreeableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GhostDeclaration;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.GhostUpdate;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptMasking;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptPriorityGet;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptPrioritySet;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptServiceRoutine;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.InterruptStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAssigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopVariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.MallocableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.NullPointer;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 28.02.2012
 */
public class ACSLHandler implements IACSLHandler {

	/**
	 * To determine the right names, we need to know where we are in the specification.
	 */

	private enum SPEC_TYPE {
		/**
		 * Not specified.
		 */
		NOT,
		/**
		 * ACSL requires statement.
		 */
		REQUIRES,
		/**
		 * ACSL assigns statement.
		 */
		ASSIGNS,
		/**
		 * ACSL ensures statement.
		 */
		ENSURES
	}

	/**
	 * Holds the spec type, which we need later in the code.
	 */
	private ACSLHandler.SPEC_TYPE mSpecType = ACSLHandler.SPEC_TYPE.NOT;
	/**
	 * in the witness invariant mode we write a different annotation at the assert
	 */
	private final boolean mWitnessInvariantMode;

	private final FlatSymbolTable mSymboltable;
	private final ExpressionTranslation mExpressionTranslation;
	private final ITypeHandler mTypeHandler;
	private final ProcedureManager mProcedureManager;
	private final ExpressionResultTransformer mExprResultTransformer;
	private final LocationFactory mLocationFactory;
	private final CHandler mCHandler;
	private final CExpressionTranslator mCExpressionTranslator;
	private final IMemoryPointer mMemoryPointer;
	private final InterruptFunctionHandler mInterruptFuncHandler;
	private final InterruptRequestHandler mIrqHandler;

	private final ScopedHashMap<String, LRValue> mBoundVariables = new ScopedHashMap<>();

	public ACSLHandler(final boolean witnessInvariantMode, final FlatSymbolTable symboltable,
			final ExpressionTranslation expressionTranslation, final ITypeHandler typeHandler,
			final ProcedureManager procedureManager, final LocationFactory locationFactory, final CHandler chandler,
			final IMemoryPointer memoryPointer, final InterruptFunctionHandler interruptFuncHandler,
			final InterruptRequestHandler irqHandler) {
		mWitnessInvariantMode = witnessInvariantMode;
		mSymboltable = symboltable;
		mExpressionTranslation = expressionTranslation;
		mTypeHandler = typeHandler;
		mProcedureManager = procedureManager;
		mExprResultTransformer = chandler.getExpressionResultTransformer();
		mLocationFactory = locationFactory;
		// Use a copy of CExpressionTranslator, where all checks for UB are disabled.
		mCExpressionTranslator = chandler.getCExpressionTranslator().disableChecksForUndefinedBehavior();
		mCHandler = chandler;
		mMemoryPointer = memoryPointer;
		mInterruptFuncHandler = interruptFuncHandler;
		mIrqHandler = irqHandler;
	}

	@Override
	public Result visit(final IDispatcher main, final ACSLNode node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final String msg = "ACSLHandler: Not yet implemented: " + node.toString();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final IDispatcher main, final OldValueExpression node) {
		return handleOldExpression(mLocationFactory.createACSLLocation(node), main, node.getExpression());
	}

	@Override
	public Result visit(final IDispatcher main, final AtLabelExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		switch (node.getLabel()) {
		case "Old":
			// TODO: Check that the context is a contract
			return handleOldExpression(loc, main, node.getExpression());
		case "Pre":
			// TODO: Check that the context is a statement annotation
			return handleOldExpression(loc, main, node.getExpression());
		case "Here":
		case "Post":
		case "LoopEntry":
		case "LoopCurrent":
		case "Init":
			// TODO: Support other built-in labels
			throw new UnsupportedSyntaxException(loc,
					node.getLabel() + " is currently not supported as a label in \\at.");
		default:
			throw new UnsupportedSyntaxException(loc,
					"Only built-in labels are currently supported as a in \\at (found ." + node.getLabel() + ").");
		}
	}

	private Result handleOldExpression(final ILocation loc, final IDispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression inner) {
		final ExpressionResult result = dispatchSwitch(main, inner, loc);
		if (!result.hasNoSideEffects()) {
			throw new UnsupportedSyntaxException(loc, "old can only be used for expressions without side-effects.");
		}
		final RValue newRValue = new RValue(ExpressionFactory.constructUnaryExpression(loc,
				UnaryExpression.Operator.OLD, result.getLrValue().getValue()), result.getLrValue().getCType());
		return new ExpressionResultBuilder().addAllExceptLrValue(result).setLrValue(newRValue).build();
	}

	@Override
	public Result visit(final IDispatcher main, final CodeAnnot node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		if (node instanceof CodeAnnotStmt) {
			final CodeStatement codeStmt = ((CodeAnnotStmt) node).getCodeStmt();
			if (codeStmt instanceof Assertion) {
				return handleAssert(main, loc, (Assertion) codeStmt);
			}
			if (codeStmt instanceof GhostUpdate) {
				return handleGhostUpdate(main, loc, (GhostUpdate) codeStmt);
			}
			if (codeStmt instanceof GhostDeclaration) {
				return handleGhostDeclaration(main, loc, (GhostDeclaration) codeStmt);
			}
		}
		throw new UnsupportedSyntaxException(loc, "ACSLHandler: Not yet implemented: " + node.toString());
	}

	private Result handleAssert(final IDispatcher main, final ILocation loc, final Assertion assertion) {
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		ExpressionResult formula = dispatchSwitch(main, assertion.getFormula(), loc);

		formula = mExprResultTransformer.rexIntToBool(formula, loc);

		resultBuilder.addAllExceptLrValue(formula);

		final AssertStatement assertStmt = new AssertStatement(loc, formula.getLrValue().getValue());
		// TODO: Handle havoc statements
		for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
			overapprItem.annotate(assertStmt);
		}
		resultBuilder.addStatement(assertStmt);
		resultBuilder.havocAuxVars();
		final Check check;
		if (mWitnessInvariantMode) {
			check = new Check(Spec.WITNESS_INVARIANT);
		} else {
			check = new Check(Spec.ASSERT);
		}
		check.annotate(assertStmt);
		return resultBuilder.build();
	}

	private Result handleGhostUpdate(final IDispatcher main, final ILocation loc, final GhostUpdate update) {
		final SymbolTableValue stv = mSymboltable.findCSymbol(main.getAcslHook(), update.getIdentifier());
		if (stv == null) {
			throw new IncorrectSyntaxException(loc,
					"Undeclared variable in ACSL expression: " + update.getIdentifier());
		}
		if (!stv.getBoogieName().startsWith(SFO.GHOST)) {
			throw new IncorrectSyntaxException(loc,
					"C variable " + update.getIdentifier() + " cannot be assigned in ghost statement.");
		}
		final ExpressionResult exprResult = (ExpressionResult) main.dispatch(update.getExpr(), main.getAcslHook());
		final ICType cType = stv.getCType();
		final ExpressionResult converted = mExprResultTransformer
				.makeRepresentationReadyForConversionAndRexBoolToInt(exprResult, loc, cType, main.getAcslHook());
		final VariableLHS lhs = new VariableLHS(loc, mTypeHandler.getBoogieTypeForCType(cType), stv.getBoogieName(),
				stv.getDeclarationInformation());
		return mCHandler.makeAssignment(loc, new LocalLValue(lhs, cType, null), List.of(), converted,
				main.getAcslHook());
	}

	private Result handleGhostDeclaration(final IDispatcher main, final ILocation loc, final GhostDeclaration decl) {
		final SymbolTableValue oldSymbol = mSymboltable.findCSymbol(main.getAcslHook(), decl.getIdentifier());
		if (oldSymbol != null) {
			throw new UnsupportedSyntaxException(loc,
					String.format("The ghost variable %s shadows another variable.", decl.getIdentifier()));
		}
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final String boogieName = SFO.GHOST + decl.getIdentifier();
		final ICType cType = AcslTypeUtils.translateAcslTypeToCType(decl.getType());
		final ASTType astType = mTypeHandler.cType2AstType(loc, cType);
		final Declaration boogieDecl = new VariableDeclaration(loc, new Attribute[0],
				new VarList[] { new VarList(loc, new String[] { boogieName }, astType) });
		final CDeclaration cDecl = new CDeclaration(cType, decl.getIdentifier());
		final IASTFunctionDefinition scope = CdtASTUtils.findScope(main.getAcslHook());
		DeclarationInformation declInfo;
		if (scope == null) {
			declInfo = DeclarationInformation.DECLARATIONINFO_GLOBAL;
		} else {
			declInfo = new DeclarationInformation(StorageClass.LOCAL, scope.getDeclarator().getName().toString());
		}
		mSymboltable.storeCSymbol(main.getAcslHook(), decl.getIdentifier(),
				new SymbolTableValue(boogieName, boogieDecl, astType, cDecl, declInfo, main.getAcslHook(), false));
		if (decl.getExpr() != null) {
			final ExpressionResult exprResult = (ExpressionResult) main.dispatch(decl.getExpr(), main.getAcslHook());
			final ExpressionResult converted = mExprResultTransformer
					.makeRepresentationReadyForConversionAndRexBoolToInt(exprResult, loc, cType, main.getAcslHook());
			resultBuilder.addAllIncludingLrValue(converted);
			final VariableLHS lhs =
					new VariableLHS(loc, mTypeHandler.getBoogieTypeForCType(cType), boogieName, declInfo);
			return mCHandler.makeAssignment(loc, new LocalLValue(lhs, cType, null), List.of(), resultBuilder.build(),
					main.getAcslHook());
		}
		return resultBuilder.build();
	}

	/**
	 * Translates an ACSL binary expression operator into a boogie binary expression operator, iff there is a one to one
	 * translation - otherwise null.
	 *
	 * @param op
	 *            the ACSL binary expression operator
	 * @return the translates operator or null.
	 */
	private static Operator getBoogieBinaryExprOperator(
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator op) {
		return switch (op) {
		case ARITHDIV -> Operator.ARITHDIV;
		case ARITHMINUS -> Operator.ARITHMINUS;
		case ARITHMOD -> Operator.ARITHMOD;
		case ARITHMUL -> Operator.ARITHMUL;
		case ARITHPLUS -> Operator.ARITHPLUS;
		case BITVECCONCAT -> Operator.BITVECCONCAT;
		case COMPEQ -> Operator.COMPEQ;
		case COMPGEQ -> Operator.COMPGEQ;
		case COMPGT -> Operator.COMPGT;
		case COMPLEQ -> Operator.COMPLEQ;
		case COMPLT -> Operator.COMPLT;
		case COMPNEQ -> Operator.COMPNEQ;
		case COMPPO -> Operator.COMPPO;
		case LOGICAND -> Operator.LOGICAND;
		case LOGICIFF -> Operator.LOGICIFF;
		case LOGICIMPLIES -> Operator.LOGICIMPLIES;
		case LOGICOR -> Operator.LOGICOR;

		case LOGICXOR -> null;
		case BITXOR, BITAND, BITIFF, BITIMPLIES, BITOR, BITSHIFTLEFT, BITSHIFTRIGHT -> null;
		case LTLRELEASE, LTLUNTIL, LTLWEAKUNTIL -> null;
		};
	}

	/**
	 * Translates operator of ACSL binary expression to operator of binary expression in the C AST.
	 */
	private static int getCASTBinaryExprOperator(
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator op) {
		return switch (op) {
		case ARITHDIV -> IASTBinaryExpression.op_divide;
		case ARITHMINUS -> IASTBinaryExpression.op_minus;
		case ARITHMOD -> IASTBinaryExpression.op_modulo;
		case ARITHMUL -> IASTBinaryExpression.op_multiply;
		case ARITHPLUS -> IASTBinaryExpression.op_plus;
		case BITAND -> IASTBinaryExpression.op_binaryAnd;
		case BITOR -> IASTBinaryExpression.op_binaryOr;
		case BITSHIFTLEFT -> IASTBinaryExpression.op_shiftLeft;
		case BITSHIFTRIGHT -> IASTBinaryExpression.op_shiftRight;
		case BITXOR -> IASTBinaryExpression.op_binaryXor;
		case COMPEQ -> IASTBinaryExpression.op_equals;
		case COMPGEQ -> IASTBinaryExpression.op_greaterEqual;
		case COMPGT -> IASTBinaryExpression.op_greaterThan;
		case COMPLEQ -> IASTBinaryExpression.op_lessEqual;
		case COMPLT -> IASTBinaryExpression.op_lessThan;
		case COMPNEQ -> IASTBinaryExpression.op_notequals;
		case LOGICAND -> IASTBinaryExpression.op_logicalAnd;
		case LOGICOR -> IASTBinaryExpression.op_logicalOr;

		case BITVECCONCAT, COMPPO, LOGICIFF, LOGICIMPLIES, LOGICXOR, LTLRELEASE, LTLUNTIL, LTLWEAKUNTIL, BITIFF,
				BITIMPLIES -> throw new IllegalArgumentException("don't know equivalent C operator");
		};
	}

	private ExpressionResult dispatchSwitch(final IDispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression node, final ILocation loc) {
		final ExpressionResult expr = (ExpressionResult) main.dispatch(node, main.getAcslHook());
		// Perform an unchecked switch to RValue (i.e., without checking for memsafety).
		// This also ensures that there are no read-calls for dereferences and thus allows us to use also dereferences
		// inside ACSL expressions that have to be side-effect-free (e.g., loop invariant or contracts)
		return mExprResultTransformer.switchToRValueUnchecked(expr, loc, main.getAcslHook());
	}

	@Override
	public Result visit(final IDispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final ExpressionResult left = dispatchSwitch(main, node.getLeft(), loc);
		final ExpressionResult right = dispatchSwitch(main, node.getRight(), loc);

		switch (node.getOperator()) {
		case ARITHDIV:
		case ARITHMOD:
		case ARITHMUL: {
			final ExpressionResult leftInt = mExprResultTransformer.rexBoolToInt(left, loc);
			final ExpressionResult rightInt = mExprResultTransformer.rexBoolToInt(right, loc);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return mCExpressionTranslator.handleMultiplicativeOperation(loc, op, leftInt, rightInt);
		}
		case ARITHMINUS:
		case ARITHPLUS: {
			final ExpressionResult leftInt = mExprResultTransformer.rexBoolToInt(left, loc);
			final ExpressionResult rightInt = mExprResultTransformer.rexBoolToInt(right, loc);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return mCExpressionTranslator.handleAdditiveOperation(loc, op, leftInt, rightInt);
		}
		case COMPEQ:
		case COMPNEQ: {
			final ExpressionResult leftInt = mExprResultTransformer.rexBoolToInt(left, loc);
			final ExpressionResult rightInt = mExprResultTransformer.rexBoolToInt(right, loc);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return mCExpressionTranslator.handleEqualityOperators(loc, op, leftInt, rightInt);
		}
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT: {
			final ExpressionResult leftInt = mExprResultTransformer.rexBoolToInt(left, loc);
			final ExpressionResult rightInt = mExprResultTransformer.rexBoolToInt(right, loc);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return mCExpressionTranslator.handleRelationalOperators(loc, op, leftInt, rightInt);
		}
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR: {
			final Operator op = getBoogieBinaryExprOperator(node.getOperator());
			if (op != null) {
				final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
				resultBuilder.addAllExceptLrValue(left);
				resultBuilder.addAllExceptLrValue(right);
				final ExpressionResult leftBool = mExprResultTransformer.rexIntToBool(left, loc);
				final ExpressionResult rightBool = mExprResultTransformer.rexIntToBool(right, loc);
				final Expression be = ExpressionFactory.newBinaryExpression(loc, op, leftBool.getLrValue().getValue(),
						rightBool.getLrValue().getValue());
				// TODO: Handle Ctype
				final RValue rval = new RValue(be, new CPrimitive(CPrimitives.INT), true);
				resultBuilder.setLrValue(rval);
				return resultBuilder.build();
			}
		}

		case LOGICXOR: {
			// translate into (l | r)
			// where l = left & !right
			final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
			resultBuilder.addAllExceptLrValue(right);
			final Expression notRight = ExpressionFactory.constructUnaryExpression(loc,
					UnaryExpression.Operator.LOGICNEG, right.getLrValue().getValue());
			final Expression l = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
					left.getLrValue().getValue(), notRight);
			// and r = !left & right
			final Expression notLeft = ExpressionFactory.constructUnaryExpression(loc,
					UnaryExpression.Operator.LOGICNEG, left.getLrValue().getValue());
			final Expression r = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, notLeft,
					right.getLrValue().getValue());
			final RValue rval = new RValue(ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, l, r),
					new CPrimitive(CPrimitives.INT), true);
			resultBuilder.setLrValue(rval);
			return resultBuilder.build();
		}
		case BITAND:
		case BITOR:
		case BITXOR:
			return mCExpressionTranslator.handleBitwiseArithmeticOperation(loc,
					getCASTBinaryExprOperator(node.getOperator()), left, right);
		case BITSHIFTLEFT:
		case BITSHIFTRIGHT:
			return mCExpressionTranslator.handleBitshiftOperation(loc, getCASTBinaryExprOperator(node.getOperator()),
					left, right);

		case BITIFF:
		case BITIMPLIES:

		case BITVECCONCAT:
		case COMPPO:

		case LTLRELEASE:
		case LTLUNTIL:
		case LTLWEAKUNTIL:
		default:
			final String msg = "Unknown or unsupported binary operation: " + node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(final IDispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);

		return switch (node.getOperator()) {
		case LOGICNEG -> mCExpressionTranslator.handleUnaryArithmeticOperators(loc, IASTUnaryExpression.op_not,
				dispatchSwitch(main, node.getExpr(), loc));
		case MINUS -> mCExpressionTranslator.handleUnaryArithmeticOperators(loc, IASTUnaryExpression.op_minus,
				dispatchSwitch(main, node.getExpr(), loc));
		case PLUS -> mCExpressionTranslator.handleUnaryArithmeticOperators(loc, IASTUnaryExpression.op_plus,
				dispatchSwitch(main, node.getExpr(), loc));
		case LOGICCOMPLEMENT -> mCExpressionTranslator.handleUnaryArithmeticOperators(loc, IASTUnaryExpression.op_tilde,
				dispatchSwitch(main, node.getExpr(), loc));

		// TODO: We don't have the hook available here, does null always work here?
		case POINTER -> mCHandler.handleIndirectionOperator(dispatchSwitch(main, node.getExpr(), loc), loc, null);

		case ADDROF -> handleAddressof(loc, (ExpressionResult) main.dispatch(node.getExpr(), main.getAcslHook()));

		case LTLFINALLY, LTLGLOBALLY, LTLNEXT -> throw new UnsupportedSyntaxException(loc,
				"Unknown or unsupported unary operation: " + node.getOperator());
		};
	}

	private ExpressionResult handleAddressof(final ILocation loc, final ExpressionResult res) {
		if (!(res.getLrValue() instanceof HeapLValue)) {
			throw new UnsupportedSyntaxException(loc, "ACSL addressof for variable off-heap");
		}
		final RValue rVal =
				((HeapLValue) res.getLrValue()).getAddressAsPointerRValue(mTypeHandler.getBoogiePointerType());
		return new ExpressionResultBuilder(res).resetLrValue(rVal).build();
	}

	@Override
	public Result visit(final IDispatcher main, final IntegerLiteral node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final String val = node.getValue();
		final RValue rValue = mExpressionTranslation.translateIntegerLiteral(loc, val);
		return new ExpressionResult(rValue);

	}

	@Override
	public Result visit(final IDispatcher main, final BooleanLiteral node) {
		return new ExpressionResult(new RValue(
				ExpressionFactory.createBooleanLiteral(mLocationFactory.createACSLLocation(node), node.getValue()),
				new CPrimitive(CPrimitives.BOOL), true));
	}

	@Override
	public Result visit(final IDispatcher main, final RealLiteral node) {
		final RValue rValue = mExpressionTranslation.translateFloatingLiteral(mLocationFactory.createACSLLocation(node),
				node.getValue());
		return new ExpressionResult(rValue);
	}

	@Override
	public Result visit(final IDispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression node) {
		final var boundVar = mBoundVariables.get(node.getIdentifier());
		if (boundVar != null) {
			return new ExpressionResult(boundVar);
		}
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final String id = lookupId(main, node, loc);

		final String cId = mSymboltable.getCIdForBoogieId(id);
		final SymbolTableValue stv = mSymboltable.findCSymbol(main.getAcslHook(), cId);
		final ICType cType;
		if (stv != null) {
			cType = stv.getCType();
		} else {
			throw new UnsupportedOperationException(
					"not yet implemented: " + "unable to determine CType for variable " + id);
		}
		final LRValue lrVal;
		if (mCHandler.isHeapVar(id)) {
			final IdentifierExpression idExp = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(stv.getAstType()), id, stv.getDeclarationInformation());
			lrVal = LRValueFactory.constructHeapLValue(mTypeHandler, idExp, cType, null);
		} else {
			final VariableLHS idLhs = ExpressionFactory.constructVariableLHS(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(stv.getAstType()), id, stv.getDeclarationInformation());
			lrVal = new LocalLValue(idLhs, cType, null);
		}
		return new ExpressionResult(lrVal);
	}

	private String lookupId(final IDispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression node, final ILocation loc) {

		final String rslvId =
				mSymboltable.applyMultiparseRenaming(main.getAcslHook().getContainingFilename(), node.getIdentifier());

		final SymbolTableValue stv = mSymboltable.findCSymbol(main.getAcslHook(), rslvId);
		if (stv == null) {
			throw new IncorrectSyntaxException(loc, "Undeclared variable in ACSL expression: " + node.getIdentifier());
		}
		return switch (mSpecType) {
		case ASSIGNS:
			// modifies case in boogie, should be always global!
			// maybe it is allowed to assign also in parameters?
			// Global variable
			if (stv.isBoogieGlobalVar()) {
				yield stv.getBoogieName();
			}
			throw new IncorrectSyntaxException(loc,
					"It is not allowed to assign to in parameters! Should be global variables! [" + node.getIdentifier()
							+ "]");
		case ENSURES:
			if ("\result".equalsIgnoreCase(node.getIdentifier())) {
				yield SFO.RES;
			}
			yield stv.getBoogieName();
		case REQUIRES:
		case NOT:
			yield stv.getBoogieName();
		};
	}

	@Override
	public Result visit(final IDispatcher main, final QuantifierExpression node) {
		mBoundVariables.beginScope();
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final List<VarList> quantifiedVars = new ArrayList<>();
		final List<Expression> typeConstraints = new ArrayList<>();
		for (final var decl : node.getVariables()) {
			// For each quantified variable in the ACSL expression, create a corresponding Boogie variable and store it
			// in the mBoundVariables to be used when handling IdentifierExpressions.
			final ICType cType = AcslTypeUtils.translateAcslTypeToCType(decl.getType());
			if (!(cType instanceof CPrimitive)) {
				throw new UnsupportedSyntaxException(loc, "Only quantified variables of primitive type are supported.");
			}
			final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.QUANTIFIED, null);
			final BoogieType boogieType = mTypeHandler.getBoogieTypeForCType(cType);
			final String name = decl.getName();
			mBoundVariables.put(name, new LocalLValue(new VariableLHS(loc, boogieType, name, declInfo), cType, false));
			quantifiedVars.add(new VarList(loc, new String[] { name }, mTypeHandler.cType2AstType(loc, cType)));
			// Collect the type constraints for the given CType (if any)
			final var id = ExpressionFactory.constructIdentifierExpression(loc, boogieType, name, declInfo);
			final var constraint = mExpressionTranslation.getTypeConstraint(loc, id, cType);
			if (constraint.isPresent()) {
				typeConstraints.add(constraint.get());
			}
		}
		final ExpressionResult subResult =
				mExprResultTransformer.rexIntToBool(dispatchSwitch(main, node.getSubformula(), loc), loc);
		if (!subResult.hasNoSideEffects()) {
			throw new UnsupportedSyntaxException(loc, "Unable to handle quantified expressions with side-effects.");
		}
		// Create a quantifier expression in Boogie
		// As Boogie uses mathematical integers, we add type constraints inside the quantifier, i.e., we produce
		// (exists ... typeConstraints && subResult) and (forall ... typeConstraints ==> subResult)
		final Expression inner = ExpressionFactory.newBinaryExpression(loc,
				node.isUniversal() ? Operator.LOGICIMPLIES : Operator.LOGICAND,
				ExpressionFactory.and(loc, typeConstraints), subResult.getLrValue().getValue());
		final Expression result = ExpressionFactory.quantifier(loc, node.isUniversal(), quantifiedVars, inner);
		mBoundVariables.endScope();
		return new ExpressionResult(new RValue(result, new CPrimitive(CPrimitives.BOOL), true));
	}

	@Override
	public Result visit(final IDispatcher main, final Contract node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);

		final ArrayList<Specification> spec = new ArrayList<>();
		for (final ContractStatement stmt : node.getContractStmt()) {
			spec.addAll(Arrays.asList(((ContractResult) main.dispatch(stmt, main.getAcslHook())).getSpecs()));
		}

		if (node.getInterruptStmt() != null) {
			for (final InterruptStatement stmt : node.getInterruptStmt()) {
				final InterruptResult res = (InterruptResult) main.dispatch(stmt, main.getAcslHook());
				mInterruptFuncHandler.register(res.getInterruptFunction());
			}
		}

		if (node.getBehaviors() != null && node.getBehaviors().length != 0) {
			final String msg = "Not yet implemented: Behaviour";
			throw new UnsupportedSyntaxException(loc, msg);
		}

		// TODO : node.getCompleteness();
		mSpecType = ACSLHandler.SPEC_TYPE.NOT;
		return new ContractResult(spec.toArray(new Specification[spec.size()]));
	}

	@Override
	public Result visit(final IDispatcher main, final InterruptServiceRoutine node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression expr = node.getIdentifier();

		if (expr instanceof final de.uni_freiburg.informatik.ultimate.model.acsl.ast.StringLiteral literal) {
			final String irqName = literal.getValue();
			final SymbolTableValue symbol = mSymboltable.findCSymbol(main.getAcslHook(), irqName);
			if (symbol != null) {
				// Lookup enum specifier from identifier name and use static value of specifier as IRQ number
				if (CEnum.replaceEnumWithInt(symbol.getCType()).getUnderlyingType().isIntegerType() && symbol
						.getConstantValue() instanceof final de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral specifier) {
					final int irqNum = Integer.parseInt(specifier.getValue());
					if (!mIrqHandler.register(irqName, irqNum)) {
						throw new UnsupportedSyntaxException(loc,
								"InterruptRequest '" + irqName + "' of InterruptServiceRoutine cannot be registered");
					} else {
						return new InterruptResult(new InterruptServiceFunction(proc, mIrqHandler.getIrq(irqName)));
					}
				} else {
					throw new IncorrectSyntaxException(loc,
							"InterruptServiceRoutine does not have an integer literal as enum specifier");
				}
			} else {
				// Register identifier name as IRQ name and assign free IRQ number
				if (!mIrqHandler.register(irqName)) {
					throw new UnsupportedSyntaxException(loc,
							"InterruptRequest '" + irqName + "' of InterruptServiceRoutine cannot be registered");
				} else {
					return new InterruptResult(new InterruptServiceFunction(proc, mIrqHandler.getIrq(irqName)));
				}
			}
		} else {
			throw new IncorrectSyntaxException(loc, "InterruptServiceRoutine must have a string literal as identifier");
		}

		return null;
	}

	@Override
	public Result visit(final IDispatcher main, final InterruptMasking node) {
		final InterruptMaskingFunction.Operation op = (node.getEnabled()) ? InterruptMaskingFunction.Operation.ENABLE
				: InterruptMaskingFunction.Operation.DISABLE;

		return new InterruptResult(null /* new InterruptMaskingFunction(proc, irq, op) */);
	}

	@Override
	public Result visit(final IDispatcher main, final InterruptPriorityGet node) {
		final InterruptPriorityFunction.Operation op = InterruptPriorityFunction.Operation.GET;

		return new InterruptResult(null /* new InterruptPriorityFunction(proc, irq, op) */);
	}

	@Override
	public Result visit(final IDispatcher main, final InterruptPrioritySet node) {
		final InterruptPriorityFunction.Operation op = InterruptPriorityFunction.Operation.SET;

		return new InterruptResult(null /* new InterruptPriorityFunction(proc, irq, op) */);
	}

	@Override
	public Result visit(final IDispatcher main, final Requires node) {
		mSpecType = ACSLHandler.SPEC_TYPE.REQUIRES;
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final ExpressionResult exprResult =
				mExprResultTransformer.rexIntToBool(dispatchSwitch(main, node.getFormula(), loc), loc);
		if (!exprResult.hasNoSideEffects()) {
			throw new UnsupportedSyntaxException(loc, "Requires must be translatable by a single expression");
		}

		final Expression formula = exprResult.getLrValue().getValue();
		final Check check = new Check(Spec.PRE_CONDITION);
		final ILocation reqLoc = mLocationFactory.createACSLLocation(node);
		final RequiresSpecification req = new RequiresSpecification(reqLoc, false, formula);
		check.annotate(req);
		return new ContractResult(new Specification[] { req });
	}

	@Override
	public Result visit(final IDispatcher main, final Ensures node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final ExpressionResult exprResult =
				mExprResultTransformer.rexIntToBool(dispatchSwitch(main, node.getFormula(), loc), loc);
		if (!exprResult.hasNoSideEffects()) {
			throw new UnsupportedSyntaxException(loc, "Ensures must be translatable by a single expression");
		}
		mSpecType = ACSLHandler.SPEC_TYPE.ENSURES;

		final Expression formula = exprResult.getLrValue().getValue();
		final Check check = new Check(Spec.POST_CONDITION);
		final ILocation ensLoc = mLocationFactory.createACSLLocation(node);
		final EnsuresSpecification ens = new EnsuresSpecification(ensLoc, false, formula);
		check.annotate(ens);
		return new ContractResult(new Specification[] { ens });
	}

	@Override
	public Result visit(final IDispatcher main, final Assigns node) {
		mSpecType = ACSLHandler.SPEC_TYPE.ASSIGNS;
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final List<IdentifierExpression> identifiers = new ArrayList<>();
		for (final de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression e : node.getLocations()) {
			if (e instanceof de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression) {
				final IdentifierExpression dispatched =
						(IdentifierExpression) main.dispatch(e, main.getAcslHook()).getNode();
				identifiers.add(dispatched);
			} else {
				final String msg = "Unexpected Expression: " + e.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}
		final VariableLHS[] identifiersVarLHS = new VariableLHS[identifiers.size()];
		for (int i = 0; i < identifiers.size(); i++) {
			identifiersVarLHS[i] =
					ExpressionFactory.constructVariableLHS(loc, (BoogieType) identifiers.get(i).getType(),
							identifiers.get(i).getIdentifier(), identifiers.get(i).getDeclarationInformation());
		}

		final ModifiesSpecification req = new ModifiesSpecification(loc, false, identifiersVarLHS);
		return new ContractResult(new Specification[] { req });
	}

	@Override
	public Result visit(final IDispatcher main, final ACSLResultExpression node) {
		final String id = SFO.RES;
		final CACSLLocation loc = mLocationFactory.createACSLLocation(node);
		final ICType type = mProcedureManager.getReturnTypeOfCurrentProcedure();
		final IdentifierExpression idEx = ExpressionFactory.constructIdentifierExpression(loc,
				mTypeHandler.getBoogieTypeForCType(type), id,
				new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, mProcedureManager.getCurrentProcedureID()));
		return new ExpressionResult(new RValue(idEx, type));
	}

	@Override
	public Result visit(final IDispatcher main, final LoopAnnot node) {
		if (node.getLoopBehavior() != null && node.getLoopBehavior().length != 0) {
			final String msg = "Not yet implemented: Behaviour";
			final ILocation loc = mLocationFactory.createACSLLocation(node);
			throw new UnsupportedSyntaxException(loc, msg);
		}
		final ArrayList<Specification> specs = new ArrayList<>();
		for (final LoopStatement lst : node.getLoopStmt()) {
			final ContractResult res = (ContractResult) main.dispatch(lst, main.getAcslHook());
			assert res != null;
			specs.addAll(Arrays.asList(res.getSpecs()));
		}
		return new ContractResult(specs.toArray(new Specification[specs.size()]));
	}

	@Override
	public Result visit(final IDispatcher main, final LoopInvariant node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final ExpressionResult res =
				mExprResultTransformer.rexIntToBool(dispatchSwitch(main, node.getFormula(), loc), loc);
		if (!res.hasNoSideEffects()) {
			throw new UnsupportedSyntaxException(loc, "We support only side-effect free specifications.");
		}

		assert res != null && res.getLrValue().getValue() != null;

		final Check check = new Check(Spec.INVARIANT);
		final ILocation invLoc = mLocationFactory.createACSLLocation(node);
		final LoopInvariantSpecification lis =
				new LoopInvariantSpecification(invLoc, false, res.getLrValue().getValue());
		check.annotate(lis);

		return new ContractResult(new Specification[] { lis });
	}

	@Override
	public Result visit(final IDispatcher main, final LoopVariant node) {
		final String msg = "Not yet implemented: LoopVariant";
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final IDispatcher main, final LoopAssigns node) {
		final String msg = "Not yet implemented: LoopAssigns";
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final IDispatcher main, final ArrayAccessExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final ExpressionResult array = (ExpressionResult) main.dispatch(node.getArray(), main.getAcslHook());
		final ExpressionResult index = dispatchSwitch(main, node.getIndex(), loc);
		return mCHandler.handleArraySubscriptExpression(array, index, main.getAcslHook());
	}

	@Override
	public Result visit(final IDispatcher main, final FieldAccessExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final ExpressionResult r = dispatchSwitch(main, node.getStruct(), loc);
		assert r.getClass() == ExpressionResult.class;
		final String field = node.getField();

		resultBuilder.addAllExceptLrValue(r);

		// TODO: CType
		final StructAccessExpression structAccessExpression =
				ExpressionFactory.constructStructAccessExpression(loc, r.getLrValue().getValue(), field);

		final RValue rval = new RValue(structAccessExpression,
				((CStructOrUnion) r.getLrValue().getCType().getUnderlyingType()).getFieldType(field));
		resultBuilder.setLrValue(rval);
		return resultBuilder.build();
	}

	@Override
	public Result visit(final IDispatcher main, final FreeableExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getExpression(), main.getAcslHook());
		Expression idx = (Expression) rIdc.getNode();

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(rIdc);

		idx = ExpressionFactory.constructStructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = { idx };

		final Expression arr = ExpressionFactory.constructIdentifierExpression(loc,
				BoogieType.createArrayType(0, new BoogieType[] { BoogieType.TYPE_INT }, BoogieType.TYPE_INT), SFO.VALID,
				new DeclarationInformation(StorageClass.GLOBAL, null));

		final Expression e = ExpressionFactory.constructNestedArrayAccessExpression(loc, arr, idc);
		// TODO: CType/range type of valid array -- depends on a preference???
		final RValue rval = new RValue(e, new CPrimitive(CPrimitives.INT));
		resultBuilder.setLrValue(rval);
		return resultBuilder.build();
	}

	@Override
	public Result visit(final IDispatcher main, final MallocableExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getExpression(), main.getAcslHook());
		Expression idx = rIdc.getLrValue().getValue();

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		resultBuilder.addAllExceptLrValue(rIdc);

		idx = ExpressionFactory.constructStructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = { idx };
		final Expression arr = ExpressionFactory.constructIdentifierExpression(loc,
				BoogieType.createArrayType(0, new BoogieType[] { BoogieType.TYPE_INT }, BoogieType.TYPE_INT), SFO.VALID,
				new DeclarationInformation(StorageClass.GLOBAL, null));
		final Expression valid = ExpressionFactory.constructNestedArrayAccessExpression(loc, arr, idc);
		final Expression e = ExpressionFactory.constructUnaryExpression(loc,
				de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator.LOGICNEG, valid);

		// TODO: CType
		final RValue rval = new RValue(e, new CPrimitive(CPrimitives.INT));
		resultBuilder.setLrValue(rval);
		return resultBuilder.build();
	}

	@Override
	public Result visit(final IDispatcher main, final ValidExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getExpression(), main.getAcslHook());
		Expression idx = rIdc.getLrValue().getValue();

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		resultBuilder.addAllExceptLrValue(rIdc);

		idx = ExpressionFactory.constructStructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = { idx };
		final Expression arr = ExpressionFactory.constructIdentifierExpression(loc,
				BoogieType.createArrayType(0, new BoogieType[] { BoogieType.TYPE_INT }, BoogieType.TYPE_INT), SFO.VALID,
				new DeclarationInformation(StorageClass.GLOBAL, null));
		final Expression e = ExpressionFactory.constructNestedArrayAccessExpression(loc, arr, idc);

		// TODO: CType
		final RValue rval = new RValue(e, new CPrimitive(CPrimitives.INT));
		resultBuilder.setLrValue(rval);
		return resultBuilder.build();
	}

	@Override
	public Result visit(final IDispatcher main, final CastExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		final ICType resultType = AcslTypeUtils.translateAcslTypeToCType(node.getCastedType());
		ExpressionResult expr = (ExpressionResult) main.dispatch(node.getExpression());
		expr = mExprResultTransformer.makeRepresentationReadyForConversion(expr, loc, resultType, main.getAcslHook());
		return mExprResultTransformer.performImplicitConversion(expr, resultType, loc);
	}

	@Override
	public Result visit(final IDispatcher main, final IfThenElseExpression node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		assert node.getOutgoingNodes().size() == 4;

		final ExpressionResult opCondition = dispatchSwitch(main, node.getCondition(), loc);
		final ExpressionResult opPositive = dispatchSwitch(main, node.getThenPart(), loc);
		final ExpressionResult opNegative = dispatchSwitch(main, node.getElsePart(), loc);
		return mCExpressionTranslator.handleConditionalOperator(loc, opCondition, opPositive, opNegative,
				main.getAcslHook());
	}

	@Override
	public Result visit(final IDispatcher main, final NullPointer node) {
		// \null is an extra notation for the null pointer (i.e. a shortcut for (void*)0).
		final var nullPtr = mMemoryPointer.constructNullPointer(mLocationFactory.createACSLLocation(node),
				mExpressionTranslation.getCTypeOfPointerComponents());

		return new ExpressionResult(new RValue(nullPtr, CPointer.voidPointer()));
	}

	@Override
	public Result visit(final IDispatcher main, final ACSLProblemNode node) {
		final ILocation loc = mLocationFactory.createACSLLocation(node);
		throw new UnsupportedSyntaxException(loc, "Error during parsing of ACSL (" + node.getErrorMessage() + ")");
	}
}
