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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.AExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ContractResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IACSLHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
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
	private ACSLHandler.SPEC_TYPE specType = ACSLHandler.SPEC_TYPE.NOT;
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
			final ExpressionResult inner = (ExpressionResult) main.dispatch(ove.getFormula());
			inner.switchToRValueIfNecessary(main, ((CHandler) main.mCHandler).getMemoryHandler(),
					((CHandler) main.mCHandler).mStructHandler, loc);
			inner.lrVal = new RValue(
					ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.OLD, inner.lrVal.getValue()),
					inner.lrVal.getCType());
			return inner;
		} else {
			final String msg = "ACSLHandler: Not yet implemented: " + node.toString();
			throw new UnsupportedSyntaxException(loc, msg);
		}
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
			final ArrayList<Declaration> decl = new ArrayList<Declaration>();
			final ArrayList<Statement> stmt = new ArrayList<Statement>();
			final List<Overapprox> overappr = new ArrayList<Overapprox>();
			final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

			ExpressionResult formula =
					(ExpressionResult) main.dispatch(((Assertion) ((CodeAnnotStmt) node).getCodeStmt()).getFormula());

			formula = formula.switchToRValueIfNecessary(main, ((CHandler) main.mCHandler).getMemoryHandler(),
					((CHandler) main.mCHandler).mStructHandler, loc);

			formula.rexIntToBoolIfNecessary(loc, ((CHandler) main.mCHandler).getExpressionTranslation(),
					((CHandler) main.mCHandler).getMemoryHandler());

			decl.addAll(formula.decl);
			stmt.addAll(formula.stmt);
			overappr.addAll(formula.overappr);
			auxVars.putAll(formula.auxVars);

			final AssertStatement assertStmt = new AssertStatement(loc, formula.lrVal.getValue());
			// TODO: Handle havoc statements
			for (final Overapprox overapprItem : overappr) {
				overapprItem.annotate(assertStmt);
			}
			stmt.add(assertStmt);
			final List<HavocStatement> havocs = CHandler.createHavocsForAuxVars(formula.auxVars);
			stmt.addAll(havocs);

			check.annotate(assertStmt);
			return new ExpressionResult(stmt, null, decl, auxVars, overappr);
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
	private int getCASTBinaryExprOperator(
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
		ExpressionResult left = (ExpressionResult) main.dispatch(node.getLeft());
		ExpressionResult right = (ExpressionResult) main.dispatch(node.getRight());

		final MemoryHandler memoryHandler = ((CHandler) main.mCHandler).getMemoryHandler();
		final StructHandler structHandler = ((CHandler) main.mCHandler).mStructHandler;

		left = left.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		right = right.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);

		final AExpressionTranslation expressionTranslation = ((CHandler) main.mCHandler).getExpressionTranslation();

		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		decl.addAll(left.decl);
		stmt.addAll(left.stmt);
		auxVars.putAll(left.auxVars);
		overappr.addAll(left.overappr);

		decl.addAll(right.decl);
		stmt.addAll(right.stmt);
		auxVars.putAll(right.auxVars);
		overappr.addAll(right.overappr);

		// if (left.getType() != null && //FIXME: (alex:) commenting this out bc of removal of InferredType -- replace
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
			return ((CHandler) main.mCHandler).handleMultiplicativeOperation(main, loc, null, op, left, right);
		}
		case ARITHMINUS:
		case ARITHPLUS: {
			left.rexBoolToIntIfNecessary(loc, expressionTranslation);
			right.rexBoolToIntIfNecessary(loc, expressionTranslation);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return ((CHandler) main.mCHandler).handleAdditiveOperation(main, loc, null, op, left, right);
		}
		case COMPEQ:
		case COMPNEQ: {
			left.rexBoolToIntIfNecessary(loc, expressionTranslation);
			right.rexBoolToIntIfNecessary(loc, expressionTranslation);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return ((CHandler) main.mCHandler).handleEqualityOperators(main, loc, op, left, right);
		}
		case COMPGEQ:
		case COMPGT:
		case COMPLEQ:
		case COMPLT: {
			left.rexBoolToIntIfNecessary(loc, expressionTranslation);
			right.rexBoolToIntIfNecessary(loc, expressionTranslation);
			final int op = getCASTBinaryExprOperator(node.getOperator());
			return ((CHandler) main.mCHandler).handleRelationalOperators(main, loc, op, left, right);
		}
		case LOGICAND:
		case LOGICIFF:
		case LOGICIMPLIES:
		case LOGICOR: {
			final Operator op = getBoogieBinaryExprOperator(node.getOperator());
			if (op != null) {
				left.rexIntToBoolIfNecessary(loc, ((CHandler) main.mCHandler).getExpressionTranslation(),
						memoryHandler);
				right.rexIntToBoolIfNecessary(loc, ((CHandler) main.mCHandler).getExpressionTranslation(),
						memoryHandler);
				final Expression be =
						ExpressionFactory.newBinaryExpression(loc, op, left.lrVal.getValue(), right.lrVal.getValue());
				// TODO: Handle Ctype
				return new ExpressionResult(stmt, new RValue(be, new CPrimitive(CPrimitives.INT), true), decl, auxVars,
						overappr);
				// return new Result(ExpressionFactory.newBinaryExpression(loc, op, left, right));
			}
		}

		case LOGICXOR:
			// translate into (l | r)
			// where l = left & !right
			final Expression notRight = ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG,
					right.lrVal.getValue());
			final Expression l =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, left.lrVal.getValue(), notRight);
			// and r = !left & right
			final Expression notLeft =
					ExpressionFactory.newUnaryExpression(loc, UnaryExpression.Operator.LOGICNEG, left.lrVal.getValue());
			final Expression r =
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, notLeft, right.lrVal.getValue());
			return new ExpressionResult(stmt,
					new RValue(ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, l, r),
							new CPrimitive(CPrimitives.INT), true),
					decl, auxVars, overappr);
		// return new Result(ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, l, r));
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
		ExpressionResult res = (ExpressionResult) main.dispatch(node.getExpr());

		final MemoryHandler memoryHandler = ((CHandler) main.mCHandler).getMemoryHandler();
		final StructHandler structHandler = ((CHandler) main.mCHandler).mStructHandler;

		res = res.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);

		switch (node.getOperator()) {
		case LOGICNEG:
			return ((CHandler) main.mCHandler).handleUnaryArithmeticOperators(main, loc, IASTUnaryExpression.op_not,
					res);
		case MINUS:
			return ((CHandler) main.mCHandler).handleUnaryArithmeticOperators(main, loc, IASTUnaryExpression.op_minus,
					res);
		case PLUS:
			return ((CHandler) main.mCHandler).handleUnaryArithmeticOperators(main, loc, IASTUnaryExpression.op_plus,
					res);
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
		final AExpressionTranslation expressionTranslation = ((CHandler) main.mCHandler).getExpressionTranslation();
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
		return new ExpressionResult(new RValue(
				new de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral(
						main.getLocationFactory().createACSLLocation(node), node.getValue()),
				new CPrimitive(CPrimitives.BOOL), true));
	}

	@Override
	public Result visit(final Dispatcher main, final RealLiteral node) {
		final AExpressionTranslation expressionTranslation = ((CHandler) main.mCHandler).getExpressionTranslation();
		final RValue rValue = expressionTranslation.translateFloatingLiteral(main.getLocationFactory().createACSLLocation(node),
				node.getValue());
		return new ExpressionResult(rValue);
	}

	@Override
	public Result visit(final Dispatcher main,
			final de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression node) {
		String id = SFO.EMPTY;
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		switch (specType) {
		case ASSIGNS:
			// modifies case in boogie, should be always global!
			// maybe it is allowed to assign also in parameters?
			// Global variable
			id = node.getIdentifier();
			SymbolTableValue stv = main.mCHandler.getSymbolTable().get(id, loc);
			if (stv.isBoogieGlobalVar()) {
				id = stv.getBoogieName();
			} else {
				final String msg = "It is not allowed to assign to in parameters! Should be global variables! ["
						+ node.getIdentifier() + "]";
				throw new IncorrectSyntaxException(loc, msg);
			}
			break;
		case ENSURES:
			if (node.getIdentifier().equalsIgnoreCase("\result")) {
				id = SFO.RES;
			} else {
				id = node.getIdentifier();
				stv = main.mCHandler.getSymbolTable().get(id, loc);
				id = stv.getBoogieName();
			}
			break;
		case REQUIRES:
			id = node.getIdentifier();
			stv = main.mCHandler.getSymbolTable().get(id, loc);
			id = stv.getBoogieName();
			break;
		case NOT:
			// We to handle the scope, so that we address here the right
			// variable
			final String cId = node.getIdentifier();
			id = main.mCHandler.getSymbolTable().get(cId, loc).getBoogieName();
			break;
		default:
			final String msg = "The type of specType should be in some type!";
			throw new IncorrectSyntaxException(loc, msg);
		}

		IBoogieType type = new InferredType(InferredType.Type.Unknown);
		final String cId = main.mCHandler.getSymbolTable().getCID4BoogieID(id, loc);
		final CType cType;
		if (specType != ACSLHandler.SPEC_TYPE.REQUIRES && specType != ACSLHandler.SPEC_TYPE.ENSURES) {
			// TODO : the translation is sometimes wrong, for requires and
			// ensures! i.e. when referring to inparams in ensures clauses!
			// The ensures clause will refer to the in-parameter listed in the
			// in parameter declaration. However, these variables will not be
			// changed, but only assigned to #in~NAME!
			// This cannot be solved by just appending "#in~" to all
			// identifiers, since the identifier could also refer to a global
			// variable! However, we don't know that at this moment!

			if (main.mCHandler.getSymbolTable().containsKey(cId)) {
				final ASTType astt = main.mCHandler.getSymbolTable().getTypeOfVariable(cId, loc);
				cType = main.mCHandler.getSymbolTable().get(cId, loc).getCVariable();
				type = new InferredType(astt);
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
		LRValue lrVal;
		if (((CHandler) main.mCHandler).isHeapVar(id)) {
			final IdentifierExpression idExp = new IdentifierExpression(loc, id);
			lrVal = new HeapLValue(idExp, cType);
		} else {
			final VariableLHS idLhs = new VariableLHS(loc, id);
			lrVal = new LocalLValue(idLhs, cType);
		}

		// for now, to make the error output clearer:
		// if (lrVal instanceof HeapLValue)
		// throw new UnsupportedOperationException("variables on heap are not supported in ACSL code right now.");

		return new ExpressionResult(lrVal);
		// return new Result(lrVal.getValue());
	}

	@Override
	public Result visit(final Dispatcher main, final Contract node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final ArrayList<Specification> spec = new ArrayList<Specification>();
		// First we catch the case that a contract is at a FunctionDefinition
		if (node instanceof IASTFunctionDefinition) {
			final String msg = "Syntax Error, Contracts on FunctionDefinition are not allowed";
			throw new IncorrectSyntaxException(loc, msg);
		}

		for (final ContractStatement stmt : node.getContractStmt()) {
			spec.addAll(Arrays.asList(((ContractResult) main.dispatch(stmt)).specs));
		}
		if (node.getBehaviors() != null && node.getBehaviors().length != 0) {
			final String msg = "Not yet implemented: Behaviour";
			throw new UnsupportedSyntaxException(loc, msg);
		}
		// TODO : node.getCompleteness();
		specType = ACSLHandler.SPEC_TYPE.NOT;
		return new ContractResult(spec.toArray(new Specification[spec.size()]));
	}

	@Override
	public Result visit(final Dispatcher main, final Requires node) {
		specType = ACSLHandler.SPEC_TYPE.REQUIRES;
		final Expression formula = ((ExpressionResult) main.dispatch(node.getFormula())).lrVal.getValue();
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
		specType = ACSLHandler.SPEC_TYPE.ENSURES;
		final Expression formula = ((ExpressionResult) main.dispatch(e)).lrVal.getValue();
		final Check check = new Check(Check.Spec.POST_CONDITION);
		final ILocation ensLoc = main.getLocationFactory().createACSLLocation(node, check);
		final EnsuresSpecification ens = new EnsuresSpecification(ensLoc, false, formula);
		check.annotate(ens);
		return new ContractResult(new Specification[] { ens });
	}

	@Override
	public Result visit(final Dispatcher main, final Assigns node) {
		specType = ACSLHandler.SPEC_TYPE.ASSIGNS;
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final ArrayList<String> identifiers = new ArrayList<String>();
		for (final de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression e : node.getLocations()) {
			if (e instanceof de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression) {
				identifiers.add(((IdentifierExpression) main.dispatch(e).node).getIdentifier());
			} else {
				final String msg = "Unexpected Expression: " + e.getClass();
				throw new UnsupportedSyntaxException(loc, msg);
			}
		}
		final VariableLHS[] identifiersVarLHS = new VariableLHS[identifiers.size()];
		for (int i = 0; i < identifiers.size(); i++) {
			identifiersVarLHS[i] = new VariableLHS(loc, identifiers.get(i));
		}

		final ModifiesSpecification req = new ModifiesSpecification(loc, false, identifiersVarLHS);
		return new ContractResult(new Specification[] { req });
	}

	@Override
	public Result visit(final Dispatcher main, final ACSLResultExpression node) {
		return new ExpressionResult(
				new RValue(new IdentifierExpression(main.getLocationFactory().createACSLLocation(node), "#res"),
						new CPrimitive(CPrimitives.INT)));
		// return new Result(new IdentifierExpression(LocationFactory.createACSLLocation(node), "#res"));
	}

	@Override
	public Result visit(final Dispatcher main, final LoopAnnot node) {
		if (node.getLoopBehavior() != null && node.getLoopBehavior().length != 0) {
			final String msg = "Not yet implemented: Behaviour";
			final ILocation loc = main.getLocationFactory().createACSLLocation(node);
			throw new UnsupportedSyntaxException(loc, msg);
		}
		final ArrayList<Specification> specs = new ArrayList<Specification>();
		for (final LoopStatement lst : node.getLoopStmt()) {
			final Result res = main.dispatch(lst);
			assert res != null && res.node != null;
			assert res.node instanceof Specification;
			specs.add((Specification) res.node);
		}
		return new ContractResult(specs.toArray(new Specification[specs.size()]));
	}

	@Override
	public Result visit(final Dispatcher main, final LoopInvariant node) {
		final ExpressionResult res = (ExpressionResult) main.dispatch(node.getFormula());

		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		assert res != null && res.lrVal.getValue() != null;
		assert res.lrVal.getValue() instanceof Expression;
		final Check check = new Check(Check.Spec.INVARIANT);
		final ILocation invLoc = main.getLocationFactory().createACSLLocation(node, check);
		final LoopInvariantSpecification lis = new LoopInvariantSpecification(invLoc, false, (Expression) res.node);
		check.annotate(lis);

		decl.addAll(res.decl);
		stmt.addAll(res.stmt);
		overappr.addAll(res.overappr);
		auxVars.putAll(res.auxVars);

		// return new ResultExpression(stmt, new RValue(lis, new CPrimitive(PRIMITIVE.BOOL)), decl, auxVars, overappr);
		return new Result(lis);
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
		final Stack<Expression> args = new Stack<Expression>();

		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression arr = node;
		do {
			assert arr instanceof ArrayAccessExpression;
			assert ((ArrayAccessExpression) arr).getIndices().length == 1;
			final ExpressionResult arg =
					(ExpressionResult) main.dispatch(((ArrayAccessExpression) arr).getIndices()[0]);
			assert arg.getClass() == ExpressionResult.class;
			assert arg.lrVal.getValue() instanceof Expression;
			args.push(arg.lrVal.getValue());
			arr = ((ArrayAccessExpression) arr).getArray();

			decl.addAll(arg.decl);
			stmt.addAll(arg.stmt);
			overappr.addAll(arg.overappr);
			auxVars.putAll(arg.auxVars);

		} while (arr instanceof ArrayAccessExpression);

		final Expression[] idx = new Expression[args.size()];
		Collections.reverse(args);
		args.toArray(idx);
		final ExpressionResult idExprRes = (ExpressionResult) main.dispatch(arr);

		assert idExprRes.getClass() == ExpressionResult.class;
		assert idExprRes.lrVal.getValue() instanceof Expression;
		final Expression subExpr = idExprRes.lrVal.getValue();

		decl.addAll(idExprRes.decl);
		stmt.addAll(idExprRes.stmt);
		overappr.addAll(idExprRes.overappr);
		auxVars.putAll(idExprRes.auxVars);

		// TODO: compute the CType of returned ResultExpression
		// basic idea: same as arrayType (below) except the last args.size() entries of arrayType.getDimensions() have
		// to be removed for the new type
		// CArray arrayType = (CArray) idExprRes.lrVal.cType;
		// CArray arrayType = new CArray(dimensions, idExprRes.lrVal.cType); --> wrong, i think (alex)
		// arrayType.getDimensions().length == args.size()

		Expression expr;
		if (subExpr instanceof IdentifierExpression) {
			final IdentifierExpression idEx = (IdentifierExpression) subExpr;
			final String bId = idEx.getIdentifier();
			final String cId = main.mCHandler.getSymbolTable().getCID4BoogieID(bId, loc);
			assert main.mCHandler.getSymbolTable().containsKey(cId);
			final InferredType it = new InferredType(main.mCHandler.getSymbolTable().getTypeOfVariable(cId, loc));
			expr = ExpressionFactory.constructNestedArrayAccessExpression(loc, it, idEx, idx);
		} else if (subExpr instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) subExpr;
			final StructLHS lhs = (StructLHS) BoogieASTUtil.getLHSforExpression(sae);
			final ASTType t = main.mTypeHandler.getTypeOfStructLHS(main.mCHandler.getSymbolTable(), loc, lhs);
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
		return new ExpressionResult(stmt, new RValue(expr, new CPrimitive(CPrimitives.INT)), decl, auxVars, overappr);
		// return new Result(expr);
	}

	@Override
	public Result visit(final Dispatcher main, final FieldAccessExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		final MemoryHandler memoryHandler = ((CHandler) main.mCHandler).getMemoryHandler();
		final StructHandler structHandler = ((CHandler) main.mCHandler).mStructHandler;

		final ExpressionResult r = ((ExpressionResult) main.dispatch(node.getStruct())).switchToRValueIfNecessary(main,
				memoryHandler, structHandler, loc);
		assert r.getClass() == ExpressionResult.class;
		assert r.lrVal.getValue() instanceof Expression;
		final String field = node.getField();

		decl.addAll(r.decl);
		stmt.addAll(r.stmt);
		overappr.addAll(r.overappr);
		auxVars.putAll(r.auxVars);

		// TODO: CType
		return new ExpressionResult(stmt,
				new RValue(new StructAccessExpression(loc, r.lrVal.getValue(), field),
						((CStruct) r.lrVal.getCType().getUnderlyingType()).getFieldType(field)),
				decl, auxVars, overappr);
	}

	@Override
	public Result visit(final Dispatcher main, final FreeableExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final IBoogieType it = new InferredType(InferredType.Type.Boolean);

		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getFormula());
		Expression idx = (Expression) rIdc.node;

		decl.addAll(rIdc.decl);
		stmt.addAll(rIdc.stmt);
		overappr.addAll(rIdc.overappr);
		auxVars.putAll(rIdc.auxVars);

		idx = new StructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = new Expression[] { idx };
		final Expression arr = new IdentifierExpression(loc, SFO.VALID);
		final Expression e =
				ExpressionFactory.constructNestedArrayAccessExpression(loc, it, arr, idc);
		// TODO: CType
		return new ExpressionResult(stmt, new RValue(e, new CPrimitive(CPrimitives.BOOL)), decl, auxVars, overappr);
		// return new Result(e);
	}

	@Override
	public Result visit(final Dispatcher main, final MallocableExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final IBoogieType it = new InferredType(InferredType.Type.Boolean);

		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getFormula());
		Expression idx = rIdc.lrVal.getValue();

		decl.addAll(rIdc.decl);
		stmt.addAll(rIdc.stmt);
		overappr.addAll(rIdc.overappr);
		auxVars.putAll(rIdc.auxVars);

		idx = new StructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = new Expression[] { idx };
		final Expression arr = new IdentifierExpression(loc, SFO.VALID);
		final Expression valid =
				ExpressionFactory.constructNestedArrayAccessExpression(loc, it, arr, idc);
		final Expression e = ExpressionFactory.newUnaryExpression(loc,
				// it,
				de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator.LOGICNEG, valid);

		// TODO: CType
		return new ExpressionResult(stmt, new RValue(e, new CPrimitive(CPrimitives.INT)), decl, auxVars, overappr);
		// return new Result(e);
	}

	@Override
	public Result visit(final Dispatcher main, final ValidExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final IBoogieType it = new InferredType(InferredType.Type.Boolean);

		final ArrayList<Declaration> decl = new ArrayList<Declaration>();
		final ArrayList<Statement> stmt = new ArrayList<Statement>();
		final List<Overapprox> overappr = new ArrayList<Overapprox>();
		final Map<VariableDeclaration, ILocation> auxVars = new LinkedHashMap<VariableDeclaration, ILocation>();

		final ExpressionResult rIdc = (ExpressionResult) main.dispatch(node.getFormula());
		Expression idx = (Expression) rIdc.node;

		decl.addAll(rIdc.decl);
		stmt.addAll(rIdc.stmt);
		overappr.addAll(rIdc.overappr);
		auxVars.putAll(rIdc.auxVars);

		idx = new StructAccessExpression(loc, idx, SFO.POINTER_BASE);
		final Expression[] idc = new Expression[] { idx };
		final Expression arr = new IdentifierExpression(loc, SFO.VALID);
		final Expression e =
				ExpressionFactory.constructNestedArrayAccessExpression(loc, it, arr, idc);

		// TODO: CType
		return new ExpressionResult(stmt, new RValue(e, new CPrimitive(CPrimitives.INT)), decl, auxVars, overappr);
		// return new Result(e);
	}

	@Override
	public Result visit(final Dispatcher main, final CastExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		final CPrimitive resultType = AcslTypeUtils.translateAcslTypeToCType(node.getCastedType());
		ExpressionResult expr = (ExpressionResult) main.dispatch(node.getExpression());
		final MemoryHandler memoryHandler = ((CHandler) main.mCHandler).getMemoryHandler();
		final StructHandler structHandler = ((CHandler) main.mCHandler).mStructHandler;
		expr = expr.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		final AExpressionTranslation expressionTranslation = ((CHandler) main.mCHandler).getExpressionTranslation();
		expressionTranslation.convertIfNecessary(loc, expr, resultType);
		return expr;
	}

	@Override
	public Result visit(final Dispatcher main, final IfThenElseExpression node) {
		final ILocation loc = main.getLocationFactory().createACSLLocation(node);
		assert node.getOutgoingNodes().size() == 4;

		final MemoryHandler memoryHandler = ((CHandler) main.mCHandler).getMemoryHandler();
		final StructHandler structHandler = ((CHandler) main.mCHandler).mStructHandler;

		ExpressionResult opCondition = (ExpressionResult) main.dispatch(node.getCondition());
		opCondition = opCondition.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		ExpressionResult opPositive = (ExpressionResult) main.dispatch(node.getThenPart());
		opPositive = opPositive.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		ExpressionResult opNegative = (ExpressionResult) main.dispatch(node.getElsePart());
		opNegative = opNegative.switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
		return ((CHandler) main.mCHandler).handleConditionalOperator(loc, opCondition, opPositive, opNegative);
	}

}
