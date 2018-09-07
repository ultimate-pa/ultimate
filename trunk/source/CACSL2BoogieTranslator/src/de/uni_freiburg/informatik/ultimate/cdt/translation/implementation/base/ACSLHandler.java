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
import java.util.Collections;
import java.util.List;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IACSLHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ACSLResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assertion;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CastExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnotStmt;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ContractStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FreeableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAssigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopVariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.MallocableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.OldValueExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;

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

	public ACSLHandler(final boolean witnessInvariantMode) {
		mWitnessInvariantMode = witnessInvariantMode;
	}

	/**
	 * @deprecated is not supported in this handler! Do not use!
	 */
	@Deprecated
	@Override
	public Result visit(final Dispatcher main, final IASTNode node) {
		throw new UnsupportedOperationException("Implementation Error: Use CHandler for: " + node.getClass());
	}

	@Override
	public Result visit(final Dispatcher main, final ACSLNode node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		if (node instanceof OldValueExpression) {
			final OldValueExpression ove = (OldValueExpression) node;
			final ExpressionResult inner = (ExpressionResult) main.dispatch(ove.getFormula(), main.getAcslHook());
			inner.switchToRValueIfNecessary(main, loc, main.getAcslHook());
			final RValue newRValue = new RValue(ExpressionFactory.constructUnaryExpression(loc,
					UnaryExpression.Operator.OLD, inner.getLrValue().getValue()), inner.getLrValue().getCType());
			return new ExpressionResultBuilder().addAllExceptLrValue(inner).setLrValue(newRValue).build();
		}
		final String msg = "ACSLHandler: Not yet implemented: " + node.toString();
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final CodeAnnot node) {
		if (node instanceof CodeAnnotStmt) {
			/*
			 * Result formula = main.dispatch(((Assertion) ((CodeAnnotStmt) node) .getCodeStmt()).getFormula()); Check
			 * check = new Check(Check.Spec.ASSERT); AssertStatement assertStmt = new AssertStatement(
			 * main.getLocationFactory().createACSLLocation(node, check), ((Expression) formula.node));
			 * check.addToNodeAnnot(assertStmt); return new Result(assertStmt);
			 */
			final Check check;
			if (mWitnessInvariantMode) {
				check = new Check(Check.Spec.WITNESS_INVARIANT);
			} else {
				check = new Check(Check.Spec.ASSERT);
			}
			final ILocation loc = main.getLocationFactory().createACSLLocation(node, check);
			// final ArrayList<Declaration> decl = new ArrayList<>();
			// final ArrayList<Statement> stmt = new ArrayList<>();
			// final List<Overapprox> overappr = new ArrayList<>();
			// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();

			ExpressionResult formula = (ExpressionResult) main
					.dispatch(((Assertion) ((CodeAnnotStmt) node).getCodeStmt()).getFormula(), main.getAcslHook());

			formula = formula.switchToRValueIfNecessary(main, loc, main.getAcslHook());

			formula.rexIntToBoolIfNecessary(loc, ((CHandler) main.mCHandler).getExpressionTranslation(),
					((CHandler) main.mCHandler).getMemoryHandler());

			final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
			// decl.addAll(formula.mDecl);
			// stmt.addAll(formula.mStmt);
			// overappr.addAll(formula.mOverappr);
			// auxVars.putAll(formula.mAuxVars);
			resultBuilder.addAllExceptLrValue(formula);

			final AssertStatement assertStmt = new AssertStatement(loc, formula.getLrValue().getValue());
			// TODO: Handle havoc statements
			for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
				overapprItem.annotate(assertStmt);
			}
			// stmt.add(assertStmt);
			resultBuilder.addStatement(assertStmt);
			final List<HavocStatement> havocs = CTranslationUtil.createHavocsForAuxVars(formula.mAuxVars);
			// stmt.addAll(havocs);
			resultBuilder.addStatements(havocs);

			check.annotate(assertStmt);
			// return new ExpressionResult(stmt, null, decl, auxVars, overappr);
			return resultBuilder.build();
		}
		// TODO : other cases
		final String msg = "ACSLHandler: Not yet implemented: " + node.toString();
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
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
		switch (op) {
		case ARITHDIV:
			return Operator.ARITHDIV;
		case ARITHMINUS:
			return Operator.ARITHMINUS;
		case ARITHMOD:
			return Operator.ARITHMOD;
		case ARITHMUL:
			return Operator.ARITHMUL;
		case ARITHPLUS:
			return Operator.ARITHPLUS;
		case BITVECCONCAT:
			return Operator.BITVECCONCAT;
		case COMPEQ:
			return Operator.COMPEQ;
		case COMPGEQ:
			return Operator.COMPGEQ;
		case COMPGT:
			return Operator.COMPGT;
		case COMPLEQ:
			return Operator.COMPLEQ;
		case COMPLT:
			return Operator.COMPLT;
		case COMPNEQ:
			return Operator.COMPNEQ;
		case COMPPO:
			return Operator.COMPPO;
		case LOGICAND:
			return Operator.LOGICAND;
		case LOGICIFF:
			return Operator.LOGICIFF;
		case LOGICIMPLIES:
			return Operator.LOGICIMPLIES;
		case LOGICOR:
			return Operator.LOGICOR;
		case BITXOR:
		case BITAND:
		case BITIFF:
		case BITIMPLIES:
		case BITOR:
		case LOGICXOR:
		default:
			return null;
		}
	}

	/**
	 * Translates operator of ACSL binary expression to operator of binary expression in the C AST.
	 */
	private static int getCASTBinaryExprOperator(
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator op) {
		switch (op) {
		case ARITHDIV:
			return IASTBinaryExpression.op_divide;
		case ARITHMINUS:
			return IASTBinaryExpression.op_minus;
		case ARITHMOD:
			return IASTBinaryExpression.op_modulo;
		case ARITHMUL:
			return IASTBinaryExpression.op_multiply;
		case ARITHPLUS:
			return IASTBinaryExpression.op_plus;
		case BITAND:
			break;
		case BITIFF:
			break;
		case BITIMPLIES:
			break;
		case BITOR:
			break;
		case BITVECCONCAT:
			break;
		case BITXOR:
			break;
		case COMPEQ:
			return IASTBinaryExpression.op_equals;
		case COMPGEQ:
			return IASTBinaryExpression.op_greaterEqual;
		case COMPGT:
			return IASTBinaryExpression.op_greaterThan;
		case COMPLEQ:
			return IASTBinaryExpression.op_lessEqual;
		case COMPLT:
			return IASTBinaryExpression.op_lessThan;
		case COMPNEQ:
			return IASTBinaryExpression.op_notequals;
		case COMPPO:
			break;
		case LOGICAND:
			return IASTBinaryExpression.op_logicalAnd;
		case LOGICIFF:
			break;
		case LOGICIMPLIES:
			break;
		case LOGICOR:
			return IASTBinaryExpression.op_logicalOr;
		case LOGICXOR:
			break;
		case LTLRELEASE:
			break;
		case LTLUNTIL:
			break;
		case LTLWEAKUNTIL:
			break;
		default:
			break;
		}
		throw new IllegalArgumentException("don't know equivalent C operator");
	}

	@Override
	public Result visit(final Dispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		ExpressionResult left = (ExpressionResult) main.dispatch(node.getLeft(), main.getAcslHook());
		ExpressionResult right = (ExpressionResult) main.dispatch(node.getRight(), main.getAcslHook());

		left = left.switchToRValueIfNecessary(main, loc, main.getAcslHook());
		right = right.switchToRValueIfNecessary(main, loc, main.getAcslHook());

		final CHandler mainCHandler = (CHandler) main.mCHandler;
		final ExpressionTranslation expressionTranslation = mainCHandler.getExpressionTranslation();

		// final ArrayList<Declaration> decl = new ArrayList<>();
		// final ArrayList<Statement> stmt = new ArrayList<>();
		// final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		// decl.addAll(left.mDecl);
		// stmt.addAll(left.mStmt);
		// auxVars.putAll(left.mAuxVars);
		// overappr.addAll(left.mOverappr);
		// resultBuilder.addAllExceptLrValue(left);

		// decl.addAll(right.mDecl);
		// stmt.addAll(right.mStmt);
		// auxVars.putAll(right.mAuxVars);
		// overappr.addAll(right.mOverappr);
		resultBuilder.addAllExceptLrValue(right);

		// if (left.getType() != null && //FIXME: (alex:) commenting this out bc of
		// removal of InferredType -- replace
		// with sth?
		// left.getType().equals(new InferredType(InferredType.Type.Boolean))) {
		// //convert to boolean if neccessary
		// right = ConvExpr.toBoolean(loc, right);
		// }

		switch (node.getOperator()) {
		case ARITHDIV:
		case ARITHMOD:
		case ARITHMUL: {
			left.rexBoolToIntIfNecessary(loc, expressionTranslation);
			right.rexBoolToIntIfNecessary(loc, expressionTranslation);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return mainCHandler.handleMultiplicativeOperation(main, loc, null, op, left, right, main.getAcslHook());
		}
		case ARITHMINUS:
		case ARITHPLUS: {
			left.rexBoolToIntIfNecessary(loc, expressionTranslation);
			right.rexBoolToIntIfNecessary(loc, expressionTranslation);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return mainCHandler.handleAdditiveOperation(main, loc, null, op, left, right, main.getAcslHook());
		}
		case COMPEQ:
		case COMPNEQ: {
			left.rexBoolToIntIfNecessary(loc, expressionTranslation);
			right.rexBoolToIntIfNecessary(loc, expressionTranslation);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return mainCHandler.handleEqualityOperators(main, loc, op, left, right);
		}
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT: {
			left.rexBoolToIntIfNecessary(loc, expressionTranslation);
			right.rexBoolToIntIfNecessary(loc, expressionTranslation);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return mainCHandler.handleRelationalOperators(main, loc, op, left, right);
		}
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR: {
			final Operator op = getBoogieBinaryExprOperator(node.getOperator());
			if (op != null) {
				final MemoryHandler memoryHandler = mainCHandler.getMemoryHandler();
				left.rexIntToBoolIfNecessary(loc, mainCHandler.getExpressionTranslation(), memoryHandler);
				right.rexIntToBoolIfNecessary(loc, mainCHandler.getExpressionTranslation(), memoryHandler);
				final Expression be = ExpressionFactory.newBinaryExpression(loc, op, left.getLrValue().getValue(),
						right.getLrValue().getValue());
				// TODO: Handle Ctype
				// return new ExpressionResult(stmt, new RValue(be, new
				// CPrimitive(CPrimitives.INT), true), decl, auxVars,
				// overappr);
				final RValue rval = new RValue(be, new CPrimitive(CPrimitives.INT), true);
				resultBuilder.setLrValue(rval);
				return resultBuilder.build();
			}
		}

		case LOGICXOR: {
			// translate into (l | r)
			// where l = left & !right
			final Expression notRight = ExpressionFactory.constructUnaryExpression(loc,
					UnaryExpression.Operator.LOGICNEG, right.getLrValue().getValue());
			final Expression l = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND,
					left.getLrValue().getValue(), notRight);
			// and r = !left & right
			final Expression notLeft = ExpressionFactory.constructUnaryExpression(loc,
					UnaryExpression.Operator.LOGICNEG, left.getLrValue().getValue());
			final Expression r = ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, notLeft,
					right.getLrValue().getValue());
			// return new ExpressionResult(stmt,
			// new RValue(ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, l,
			// r),
			// new CPrimitive(CPrimitives.INT), true),
			// decl, auxVars, overappr);
			final RValue rval = new RValue(ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, l, r),
					new CPrimitive(CPrimitives.INT), true);
			resultBuilder.setLrValue(rval);
			return resultBuilder.build();
		}
		case BITAND:
		case BITIFF:
		case BITIMPLIES:
		case BITOR:
		case BITXOR:

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
	public Result visit(final Dispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		ExpressionResult res = (ExpressionResult) main.dispatch(node.getExpr(), main.getAcslHook());

		res = res.switchToRValueIfNecessary(main, loc, main.getAcslHook());

		switch (node.getOperator()) {
		case LOGICNEG:
			return ((CHandler) main.mCHandler).handleUnaryArithmeticOperators(main, loc, IASTUnaryExpression.op_not,
					res, main.getAcslHook());
		case MINUS:
			return ((CHandler) main.mCHandler).handleUnaryArithmeticOperators(main, loc, IASTUnaryExpression.op_minus,
					res, main.getAcslHook());
		case PLUS:
			return ((CHandler) main.mCHandler).handleUnaryArithmeticOperators(main, loc, IASTUnaryExpression.op_plus,
					res, main.getAcslHook());
		case POINTER:
		case ADDROF:
		case LOGICCOMPLEMENT:
		default:
			final String msg = "Unknown or unsupported unary operation: " + node.getOperator();
			throw new UnsupportedSyntaxException(loc, msg);
		}
	}

	@Override
	public Result visit(final Dispatcher main, final IntegerLiteral node) {
		/*
		 * return new Result( new de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral(
		 * LocationFactory.createACSLLocation(node), node.getValue()));
		 */
		final ExpressionTranslation expressionTranslation = ((CHandler) main.mCHandler).getExpressionTranslation();
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final String val = node.getValue();
		final RValue rValue = expressionTranslation.translateIntegerLiteral(loc, val);
		return new ExpressionResult(rValue);

	}

	@Override
	public Result visit(final Dispatcher main, final BooleanLiteral node) {
		/*
		 * return new Result( new de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral(
		 * LocationFactory.createACSLLocation(node), node.getValue()));
		 */
		return new ExpressionResult(
				new RValue(ExpressionFactory.createBooleanLiteral(main.getLocationFactory().createACSLLocation(node),
						node.getValue()), new CPrimitive(CPrimitives.BOOL), true));
	}

	@Override
	public Result visit(final Dispatcher main, final RealLiteral node) {
		final ExpressionTranslation expressionTranslation = ((CHandler) main.mCHandler).getExpressionTranslation();
		final RValue rValue = expressionTranslation
				.translateFloatingLiteral(main.getLocationFactory().createACSLLocation(node), node.getValue());
		return new ExpressionResult(rValue);
	}

	@Override
	public Result visit(final Dispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final String id = lookupId(main, node, loc);

		final String cId = main.mCHandler.getSymbolTable().getCIdForBoogieId(id);
		final CType cType;
		SymbolTableValue stv;
		if (mSpecType != ACSLHandler.SPEC_TYPE.REQUIRES && mSpecType != ACSLHandler.SPEC_TYPE.ENSURES) {
			// TODO : the translation is sometimes wrong, for requires and
			// ensures! i.e. when referring to inparams in ensures clauses!
			// The ensures clause will refer to the in-parameter listed in the
			// in parameter declaration. However, these variables will not be
			// changed, but only assigned to #in~NAME!
			// This cannot be solved by just appending "#in~" to all
			// identifiers, since the identifier could also refer to a global
			// variable! However, we don't know that at this moment!

			if (main.mCHandler.getSymbolTable().containsCSymbol(main.getAcslHook(), cId)) {
				stv = main.mCHandler.getSymbolTable().findCSymbol(main.getAcslHook(), cId);
				cType = stv.getCVariable();
			} else {
				throw new UnsupportedOperationException(
						"not yet implemented: " + "unable to determine CType for variable " + id);
			}
		} else {
			throw new UnsupportedOperationException(
					"not yet implemented: " + "unable to determine CType for variable " + id);
		}

		// FIXME: dereferencing does not work for ACSL yet, because we cannot pass
		// the necessary auxiliary statements on.
		// EDIT: (alex feb 18:) does this fixme still apply?

		// TODO seems quite hacky, how we obtain storage class and procedure id ..
		final ASTType astType;
		if (stv.getBoogieDecl() instanceof VariableDeclaration) {
			astType = ((VariableDeclaration) stv.getBoogieDecl()).getVariables()[0].getType();
		} else if (stv.getBoogieDecl() instanceof ConstDeclaration) {
			astType = ((ConstDeclaration) stv.getBoogieDecl()).getVarList().getType();
		} else {
			throw new UnsupportedOperationException("todo: handle this case");
		}
		final StorageClass sc = stv.isBoogieGlobalVar() ? StorageClass.GLOBAL : StorageClass.LOCAL;
		final String procId =
				sc == StorageClass.GLOBAL ? null : main.mCHandler.getProcedureManager().getCurrentProcedureID();
		LRValue lrVal;
		if (((CHandler) main.mCHandler).isHeapVar(id)) {
			final IdentifierExpression idExp = // new IdentifierExpression(loc, id);
					ExpressionFactory.constructIdentifierExpression(loc,
							main.mCHandler.getBoogieTypeHelper().getBoogieTypeForBoogieASTType(astType), id,
							new DeclarationInformation(sc, procId));
			lrVal = LRValueFactory.constructHeapLValue(main, idExp, cType, null);
		} else {
			final VariableLHS idLhs = // new VariableLHS(loc, id);
					ExpressionFactory.constructVariableLHS(loc,
							main.mCHandler.getBoogieTypeHelper().getBoogieTypeForBoogieASTType(astType), id,
							new DeclarationInformation(sc, procId));
			lrVal = new LocalLValue(idLhs, cType, null);
		}

		// for now, to make the error output clearer:
		// if (lrVal instanceof HeapLValue)
		// throw new UnsupportedOperationException("variables on heap are not supported
		// in ACSL code right now.");

		return new ExpressionResult(lrVal);
		// return new Result(lrVal.getValue());
	}

	private String lookupId(final Dispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression node, final ILocation loc) {

		final String rslvId = main.mCHandler.getSymbolTable()
				.applyMultiparseRenaming(main.getAcslHook().getContainingFilename(), node.getIdentifier());

		final SymbolTableValue stv = main.mCHandler.getSymbolTable().findCSymbol(main.getAcslHook(), rslvId);
		if (stv == null) {
			throw new IncorrectSyntaxException(loc, "Undeclared variable in ACSL expression: " + node.getIdentifier());
		}
		switch (mSpecType) {
		case ASSIGNS:
			// modifies case in boogie, should be always global!
			// maybe it is allowed to assign also in parameters?
			// Global variable
			if (stv.isBoogieGlobalVar()) {
				return stv.getBoogieName();
			}
			throw new IncorrectSyntaxException(loc,
					"It is not allowed to assign to in parameters! Should be global variables! [" + node.getIdentifier()
							+ "]");
		case ENSURES:
			if ("\result".equalsIgnoreCase(node.getIdentifier())) {
				return SFO.RES;
			}
			return stv.getBoogieName();
		case REQUIRES:
		case NOT:
			return stv.getBoogieName();
		default:
			throw new IncorrectSyntaxException(loc, "The type of specType should be in some type!");
		}
	}

	@Override
	public Result visit(final Dispatcher main, final Contract node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final ArrayList<Specification> spec = new ArrayList<>();
		// First we catch the case that a contract is at a FunctionDefinition
		if (node instanceof IASTFunctionDefinition) {
			final String msg = "Syntax Error, Contracts on FunctionDefinition are not allowed";
			throw new IncorrectSyntaxException(loc, msg);
		}

		for (final ContractStatement stmt : node.getContractStmt()) {
			spec.addAll(Arrays.asList(((ContractResult) main.dispatch(stmt, main.getAcslHook())).getSpecs()));
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
	public Result visit(final Dispatcher main, final Requires node) {
		mSpecType = ACSLHandler.SPEC_TYPE.REQUIRES;
		final Expression formula = ((ExpressionResult) main.dispatch(node.getFormula())).getLrValue().getValue();
		final Check check = new Check(Check.Spec.PRE_CONDITION);
		final ILocation reqLoc = main.getLocationFactory().createACSLLocation(node, check);
		final RequiresSpecification req = new RequiresSpecification(reqLoc, false, formula);
		check.annotate(req);
		return new ContractResult(new Specification[] { req });
	}

	@Override
	public Result visit(final Dispatcher main, final Ensures node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression e = node.getFormula();
		if (e instanceof FieldAccessExpression || e instanceof ArrayAccessExpression) {
			// variable declaration not yet translated, hence we cannot
			// translate this access expression!
			final String msg = "Ensures specification on struct types is not supported!";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		mSpecType = ACSLHandler.SPEC_TYPE.ENSURES;
		final Expression formula = ((ExpressionResult) main.dispatch(e)).getLrValue().getValue();
		final Check check = new Check(Check.Spec.POST_CONDITION);
		final ILocation ensLoc = main.getLocationFactory().createACSLLocation(node, check);
		final EnsuresSpecification ens = new EnsuresSpecification(ensLoc, false, formula);
		check.annotate(ens);
		return new ContractResult(new Specification[] { ens });
	}

	@Override
	public Result visit(final Dispatcher main, final Assigns node) {
		mSpecType = ACSLHandler.SPEC_TYPE.ASSIGNS;
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final List<IdentifierExpression> identifiers = new ArrayList<>();
		for (final de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression e : node.getLocations()) {
			if (e instanceof de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression) {
				final IdentifierExpression dispatched =
						((IdentifierExpression) main.dispatch(e, main.getAcslHook()).node);
				// identifiers.add(dispatched.getIdentifier());
				identifiers.add(dispatched);
			} else {
				final String msg = "Unexpected Expression: " + e.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}
		final VariableLHS[] identifiersVarLHS = new VariableLHS[identifiers.size()];
		for (int i = 0; i < identifiers.size(); i++) {
			identifiersVarLHS[i] = // new VariableLHS(loc, identifiers.get(i));
					ExpressionFactory.constructVariableLHS(loc, (BoogieType) identifiers.get(i).getType(),
							identifiers.get(i).getIdentifier(), identifiers.get(i).getDeclarationInformation());
		}

		final ModifiesSpecification req = new ModifiesSpecification(loc, false, identifiersVarLHS);
		return new ContractResult(new Specification[] { req });
	}

	@Override
	public Result visit(final Dispatcher main, final ACSLResultExpression node) {
		final String id = "#res";
		final CACSLLocation loc = main.getLocationFactory().createACSLLocation(node);
		// TODO: what is the right storageclass here? and procedure?..
		final IdentifierExpression idEx = // new IdentifierExpression(loc, "#res");
				ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT, id,
						new DeclarationInformation(StorageClass.LOCAL,
								main.mCHandler.getProcedureManager().getCurrentProcedureID()));
		return new ExpressionResult(new RValue(idEx, new CPrimitive(CPrimitives.INT)));
		// return new Result(new
		// IdentifierExpression(LocationFactory.createACSLLocation(node), "#res"));
	}

	@Override
	public Result visit(final Dispatcher main, final LoopAnnot node) {
		if (node.getLoopBehavior() != null && node.getLoopBehavior().length != 0) {
			final String msg = "Not yet implemented: Behaviour";
			final ILocation loc = main.getLocationFactory().createACSLLocation(node);
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
	public Result visit(final Dispatcher main, final LoopInvariant node) {
		final ExpressionResult res = (ExpressionResult) main.dispatch(node.getFormula(), main.getAcslHook());
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		if (!res.getAuxVars().isEmpty()) {
			throw new UnsupportedSyntaxException(loc, "We support only side-effect free specifications.");
		}
		if (!res.getDeclarations().isEmpty()) {
			throw new UnsupportedSyntaxException(loc, "We support only side-effect free specifications.");
		}
		if (!res.getNeighbourUnionFields().isEmpty()) {
			throw new UnsupportedSyntaxException(loc, "We support only side-effect free specifications.");
		}
		if (!res.getOverapprs().isEmpty()) {
			throw new UnsupportedSyntaxException(loc,
					"We support only contracts that we can translate without overapproximation.");
		}

		assert res != null && res.getLrValue().getValue() != null;
		final Check check = new Check(Check.Spec.INVARIANT);
		final ILocation invLoc = main.getLocationFactory().createACSLLocation(node, check);
		final LoopInvariantSpecification lis = new LoopInvariantSpecification(invLoc, false, res.getLrValue().getValue());
		check.annotate(lis);

		return new ContractResult(new Specification[] { lis } );
	}

	@Override
	public Result visit(final Dispatcher main, final LoopVariant node) {
		final String msg = "Not yet implemented: LoopVariant";
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final LoopAssigns node) {
		final String msg = "Not yet implemented: LoopAssigns";
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		throw new UnsupportedSyntaxException(loc, msg);
	}

	@Override
	public Result visit(final Dispatcher main, final ArrayAccessExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final Stack<Expression> args = new Stack<>();

		// final ArrayList<Declaration> decl = new ArrayList<>();
		// final ArrayList<Statement> stmt = new ArrayList<>();
		// final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression arr = node;
		do {
			assert arr instanceof ArrayAccessExpression;
			assert ((ArrayAccessExpression) arr).getIndices().length == 1;
			final ExpressionResult arg =
					(ExpressionResult) main.dispatch(((ArrayAccessExpression) arr).getIndices()[0], main.getAcslHook());
			assert arg.getClass() == ExpressionResult.class;
			args.push(arg.getLrValue().getValue());
			arr = ((ArrayAccessExpression) arr).getArray();

			// decl.addAll(arg.mDecl);
			// stmt.addAll(arg.mStmt);
			// overappr.addAll(arg.mOverappr);
			// auxVars.putAll(arg.mAuxVars);
			resultBuilder.addAllExceptLrValue(arg);

		} while (arr instanceof ArrayAccessExpression);

		final Expression[] idx = new Expression[args.size()];
		Collections.reverse(args);
		args.toArray(idx);
		final ExpressionResult idExprRes = (ExpressionResult) main.dispatch(arr, main.getAcslHook());

		assert idExprRes.getClass() == ExpressionResult.class;
		final Expression subExpr = idExprRes.getLrValue().getValue();

		// decl.addAll(idExprRes.mDecl);
		// stmt.addAll(idExprRes.mStmt);
		// overappr.addAll(idExprRes.mOverappr);
		// auxVars.putAll(idExprRes.mAuxVars);
		resultBuilder.addAllExceptLrValue(idExprRes);

		// TODO: compute the CType of returned ResultExpression
		// basic idea: same as arrayType (below) except the last args.size() entries of
		// arrayType.getDimensions() have
		// to be removed for the new type
		// CArray arrayType = (CArray) idExprRes.lrVal.cType;
		// CArray arrayType = new CArray(dimensions, idExprRes.lrVal.cType); --> wrong,
		// i think (alex)
		// arrayType.getDimensions().length == args.size()

		Expression expr;
		if (subExpr instanceof IdentifierExpression) {
			final IdentifierExpression idEx = (IdentifierExpression) subExpr;
			final String bId = idEx.getIdentifier();
			final String cId = main.mCHandler.getSymbolTable().getCIdForBoogieId(bId);
			assert main.mCHandler.getSymbolTable().containsCSymbol(main.getAcslHook(), cId);
			// final InferredType it = new
			// InferredType(main.mCHandler.getSymbolTable().getTypeOfVariable(cId, loc));
			expr = ExpressionFactory.constructNestedArrayAccessExpression(loc, idEx, idx);
		} else if (subExpr instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) subExpr;
			final StructLHS lhs = (StructLHS) BoogieASTUtil.getLHSforExpression(sae);
			final ASTType t =
					main.mTypeHandler.getTypeOfStructLHS(main.mCHandler.getSymbolTable(), loc, lhs, main.getAcslHook());
			if (!(t instanceof ArrayType)) {
				final String msg = "Type mismatch - cannot take index on a not-array element!";
				throw new IncorrectSyntaxException(loc, msg);
			}
			expr = ExpressionFactory.constructNestedArrayAccessExpression(loc, sae, idx);
		} else {
			final String msg = "Unexpected result type on left side of array!";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		// TODO: Ctype
		final RValue rval = new RValue(expr, new CPrimitive(CPrimitives.INT));
		resultBuilder.setLrValue(rval);
		return resultBuilder.build();
		// return new ExpressionResult(stmt, rval, decl, auxVars, overappr);
		// return new Result(expr);
	}

	@Override
	public Result visit(final Dispatcher main, final FieldAccessExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		// final ArrayList<Declaration> decl = new ArrayList<>();
		// final ArrayList<Statement> stmt = new ArrayList<>();
		// final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		final ExpressionResult r = ((ExpressionResult) main.dispatch(node.getStruct())).switchToRValueIfNecessary(main,
				loc, main.getAcslHook());
		assert r.getClass() == ExpressionResult.class;
		final String field = node.getField();

		// decl.addAll(r.mDecl);
		// stmt.addAll(r.mStmt);
		// overappr.addAll(r.mOverappr);
		// auxVars.putAll(r.mAuxVars);
		resultBuilder.addAllExceptLrValue(r);

		// TODO: CType
		final StructAccessExpression structAccessExpression =
				ExpressionFactory.constructStructAccessExpression(loc, r.getLrValue().getValue(), field);

		final RValue rval = new RValue(structAccessExpression,
				((CStruct) r.getLrValue().getCType().getUnderlyingType()).getFieldType(field));
		// return new ExpressionResult(stmt, rval decl, auxVars, overappr);
		resultBuilder.setLrValue(rval);
		return resultBuilder.build();
	}

	@Override
	public Result visit(final Dispatcher main, final FreeableExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		// final IBoogieType it = new InferredType(InferredType.Type.Boolean);

		// final ArrayList<Declaration> decl = new ArrayList<>();
		// final ArrayList<Statement> stmt = new ArrayList<>();
		// final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getFormula(), main.getAcslHook());
		Expression idx = (Expression) rIdc.node;

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		// decl.addAll(rIdc.mDecl);
		// stmt.addAll(rIdc.mStmt);
		// overappr.addAll(rIdc.mOverappr);
		// auxVars.putAll(rIdc.mAuxVars);
		resultBuilder.addAllExceptLrValue(rIdc);

		idx = ExpressionFactory.constructStructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = new Expression[] { idx };

		final Expression arr = // new IdentifierExpression(loc, SFO.VALID);
				ExpressionFactory.constructIdentifierExpression(loc,
						BoogieType.createArrayType(0, new BoogieType[] { BoogieType.TYPE_INT }, BoogieType.TYPE_INT),
						SFO.VALID, new DeclarationInformation(StorageClass.GLOBAL, null));

		final Expression e = ExpressionFactory.constructNestedArrayAccessExpression(loc, arr, idc);
		// TODO: CType/range type of valid array -- depends on a preference???
		final RValue rval = new RValue(e, new CPrimitive(CPrimitives.INT));
		// return new ExpressionResult(stmt, rval, decl, auxVars, overappr);
		resultBuilder.setLrValue(rval);
		return resultBuilder.build();
		// return new Result(e);
	}

	@Override
	public Result visit(final Dispatcher main, final MallocableExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		// final IBoogieType it = new InferredType(InferredType.Type.Boolean);

		// final ArrayList<Declaration> decl = new ArrayList<>();
		// final ArrayList<Statement> stmt = new ArrayList<>();
		// final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getFormula(), main.getAcslHook());
		Expression idx = rIdc.getLrValue().getValue();

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		// decl.addAll(rIdc.mDecl);
		// stmt.addAll(rIdc.mStmt);
		// overappr.addAll(rIdc.mOverappr);
		// auxVars.putAll(rIdc.mAuxVars);
		resultBuilder.addAllExceptLrValue(rIdc);

		idx = ExpressionFactory.constructStructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = new Expression[] { idx };
		final Expression arr = ExpressionFactory.constructIdentifierExpression(loc,
				BoogieType.createArrayType(0, new BoogieType[] { BoogieType.TYPE_INT }, BoogieType.TYPE_INT), SFO.VALID,
				new DeclarationInformation(StorageClass.GLOBAL, null));
		final Expression valid = ExpressionFactory.constructNestedArrayAccessExpression(loc, arr, idc);
		final Expression e = ExpressionFactory.constructUnaryExpression(loc,
				// it,
				de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator.LOGICNEG, valid);

		// TODO: CType
		final RValue rval = new RValue(e, new CPrimitive(CPrimitives.INT));
		resultBuilder.setLrValue(rval);
		return resultBuilder.build();
		// return new ExpressionResult(stmt, new RValue(e, new
		// CPrimitive(CPrimitives.INT)), decl, auxVars, overappr);
		// return new Result(e);
	}

	@Override
	public Result visit(final Dispatcher main, final ValidExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		// final IBoogieType it = new InferredType(InferredType.Type.Boolean);

		// final ArrayList<Declaration> decl = new ArrayList<>();
		// final ArrayList<Statement> stmt = new ArrayList<>();
		// final List<Overapprox> overappr = new ArrayList<>();
		// final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<>();

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getFormula(), main.getAcslHook());
		Expression idx = (Expression) rIdc.node;

		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		resultBuilder.addAllExceptLrValue(rIdc);

		idx = ExpressionFactory.constructStructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = new Expression[] { idx };
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
	public Result visit(final Dispatcher main, final CastExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final CPrimitive resultType = AcslTypeUtils.translateAcslTypeToCType(node.getCastedType());
		ExpressionResult expr = (ExpressionResult) main.dispatch(node.getExpression());
		expr = expr.switchToRValueIfNecessary(main, loc, main.getAcslHook());
		final ExpressionTranslation expressionTranslation = ((CHandler) main.mCHandler).getExpressionTranslation();
		expressionTranslation.convertIfNecessary(loc, expr, resultType);
		return expr;
	}

	@Override
	public Result visit(final Dispatcher main, final IfThenElseExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		assert node.getOutgoingNodes().size() == 4;

		ExpressionResult opCondition = (ExpressionResult) main.dispatch(node.getCondition());
		opCondition = opCondition.switchToRValueIfNecessary(main, loc, main.getAcslHook());
		ExpressionResult opPositive = (ExpressionResult) main.dispatch(node.getThenPart());
		opPositive = opPositive.switchToRValueIfNecessary(main, loc, main.getAcslHook());
		ExpressionResult opNegative = (ExpressionResult) main.dispatch(node.getElsePart());
		opNegative = opNegative.switchToRValueIfNecessary(main, loc, main.getAcslHook());
		return ((CHandler) main.mCHandler).handleConditionalOperator(loc, main, opCondition, opPositive, opNegative,
				main.getAcslHook());
	}

}
