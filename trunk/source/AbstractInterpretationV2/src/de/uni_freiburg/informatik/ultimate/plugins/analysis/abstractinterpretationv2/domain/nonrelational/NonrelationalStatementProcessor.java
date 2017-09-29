/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitVectorAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.symboltable.BoogieSymbolTable;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.EvaluatorUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.INAryEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link IntervalDomainState} for the given statement.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public abstract class NonrelationalStatementProcessor<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
		extends BoogieVisitor {

	private final IBoogieSymbolTableVariableProvider mBoogie2SmtSymbolTable;
	private final BoogieSymbolTable mSymbolTable;
	private final ILogger mLogger;
	private final IEvaluatorFactory<V, STATE> mEvaluatorFactory;

	private STATE mOldState;
	private List<STATE> mReturnState;
	private ExpressionEvaluator<V, STATE> mExpressionEvaluator;
	private IProgramVarOrConst mLhsVariable;
	private Map<LeftHandSide, IProgramVarOrConst> mTemporaryVars;

	private final Map<Expression, Expression> mNormalizedExpressionCache;

	private boolean mOldScope;

	protected NonrelationalStatementProcessor(final ILogger logger, final BoogieSymbolTable boogieSymbolTable,
			final IBoogieSymbolTableVariableProvider bpl2SmtTable, final int maxParallelStates) {
		mBoogie2SmtSymbolTable = bpl2SmtTable;
		mSymbolTable = boogieSymbolTable;
		mOldScope = false;
		mLogger = logger;
		mLhsVariable = null;
		mNormalizedExpressionCache = new HashMap<>();
		mEvaluatorFactory = createEvaluatorFactory(maxParallelStates);
		assert mEvaluatorFactory != null;
	}

	public List<STATE> process(final STATE oldState, final Statement statement) {
		return process(oldState, statement, Collections.emptyMap());
	}

	public List<STATE> process(final STATE oldState, final Statement statement,
			final Map<LeftHandSide, IProgramVarOrConst> tmpVars) {
		assert oldState != null;
		assert statement != null;
		assert tmpVars != null;

		mReturnState = new ArrayList<>();
		mOldState = oldState;
		mTemporaryVars = tmpVars;
		mLhsVariable = null;

		processStatement(statement);
		final List<STATE> rtr = mReturnState;
		assert oldState.getVariables().isEmpty() || !rtr.isEmpty();

		mReturnState = null;
		mOldState = null;
		mTemporaryVars = null;
		mLhsVariable = null;

		return rtr;
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		if (statement instanceof AssignmentStatement) {
			handleAssignment((AssignmentStatement) statement);
			return statement;
		} else if (statement instanceof AssumeStatement) {
			handleAssumeStatement((AssumeStatement) statement);
			return statement;
		} else if (statement instanceof HavocStatement) {
			handleHavocStatement((HavocStatement) statement);
			return statement;
		}
		return super.processStatement(statement);
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		// TODO: implement proper array handling. Currently, TOP is returned for all array accesses.
		if (expr instanceof ArrayStoreExpression || expr instanceof ArrayAccessExpression) {
			mExpressionEvaluator.addEvaluator(mEvaluatorFactory
					.createSingletonValueTopEvaluator(EvaluatorUtils.getEvaluatorType(expr.getType())));
			return expr;
		}
		if (expr instanceof UnaryExpression) {
			final UnaryExpression uexpr = (UnaryExpression) expr;
			if (uexpr.getOperator() == Operator.OLD) {
				mOldScope = true;
				final Expression rtr = super.processExpression(uexpr.getExpr());
				mOldScope = false;
				return rtr;
			}
		}
		final Expression newExpr = createNormalizedExpression(expr);
		return super.processExpression(newExpr);
	}

	private Expression createNormalizedExpression(final Expression inputExpr) {
		final Expression rtrExpr = mNormalizedExpressionCache.get(inputExpr);
		if (rtrExpr != null) {
			return rtrExpr;
		}
		Expression oldExpr = inputExpr;
		Expression newExpr = normalizeExpression(oldExpr);
		while (newExpr != oldExpr) {
			assert newExpr != null;
			assert newExpr.getType() != null : "Normalization did set a null type";
			oldExpr = newExpr;
			newExpr = normalizeExpression(oldExpr);
		}

		if (mLogger.isDebugEnabled() && newExpr != inputExpr) {
			mLogger.debug(String.format("%sRewrote expression %s to %s", AbsIntPrefInitializer.INDENT,
					BoogiePrettyPrinter.print(inputExpr), BoogiePrettyPrinter.print(newExpr)));
		}

		mNormalizedExpressionCache.put(inputExpr, newExpr);
		return newExpr;
	}

	protected abstract IEvaluatorFactory<V, STATE> createEvaluatorFactory(final int maxParallelStates);

	/**
	 * Override this method to add evaluators for this (already preprocessed) expression.
	 *
	 * @param evaluator
	 *            The current root evaluator.
	 * @param evaluatorFactory
	 *            The current instance of the evaluator factory.
	 * @param expr
	 *            The preprocessed expression.
	 */
	protected void addEvaluators(final ExpressionEvaluator<V, STATE> evaluator,
			final IEvaluatorFactory<V, STATE> evaluatorFactory, final Expression expr) {
		// not necessary for non-relational statement processor
	}

	/**
	 * Override this method if you want to apply some sort of normalization.
	 *
	 * @param expr
	 *            The expression that is about to be processed.
	 * @return The normalized expression or the old expression, if nothing had to be changed.
	 */
	protected Expression normalizeExpression(final Expression expr) {
		return expr;
	}

	protected ILogger getLogger() {
		return mLogger;
	}

	private void handleAssignment(final AssignmentStatement statement) {
		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();
		final int count = lhs.length;
		assert lhs.length == rhs.length && count > 0 : "Broken assignment statement";

		if (count > 1) {
			handleMultiAssignment(lhs, rhs);
			return;
		}
		// it is a single assignment
		mReturnState.addAll(handleSingleAssignment(getLhsVariable(lhs[0]), rhs[0], mOldState));
	}

	private void handleMultiAssignment(final LeftHandSide[] lhs, final Expression[] rhs) {
		final List<List<STATE>> multiAssignmentResults = new ArrayList<>();
		for (int i = 0; i < lhs.length; i++) {
			final IProgramVarOrConst lhsVar = getLhsVariable(lhs[i]);
			final List<STATE> unprojectedState = handleSingleAssignment(lhsVar, rhs[i], mOldState);
			final List<STATE> projectedState = project(lhsVar, unprojectedState);
			assert projectedState != null;
			multiAssignmentResults.add(projectedState);
		}

		// now patch each of the results in the old state
		// each of the lists contains the result of one assignment; the end result has to be the cartesian product
		final List<List<STATE>> stateList = CrossProducts.crossProduct(multiAssignmentResults);
		stateList.stream().map(stateAsList -> stateAsList.stream().reduce((a, b) -> a.patch(b)))
				.forEach(a -> mReturnState.add(mOldState.patch(a.get())));
	}

	/**
	 * Project away all variables expect lhsVar from each STATE in states.
	 *
	 * @param lhsVar
	 *            The {@link IProgramVar} to keep.
	 * @param states
	 *            The states which should be projected on lhsVar.
	 * @return A {@link List} of states containing only lhsVar.
	 */
	private List<STATE> project(final IProgramVarOrConst lhsVar, final List<STATE> states) {
		return states.stream().map(a -> project(lhsVar, a)).collect(Collectors.toList());
	}

	/**
	 * Project away all variables expect lhsVar from state.
	 *
	 * @param lhsVar
	 *            The {@link IProgramVar} to keep.
	 * @param state
	 *            The state which should be projected on lhsVar.
	 * @return A STATE containing only lhsVar.
	 */
	private STATE project(final IProgramVarOrConst lhsVar, final STATE state) {
		final Set<IProgramVarOrConst> varsToRemove = new HashSet<>(state.getVariables());
		varsToRemove.remove(lhsVar);
		return state.removeVariables(varsToRemove);
	}

	private List<STATE> handleSingleAssignment(final IProgramVarOrConst lhsVar, final Expression rhs,
			final STATE oldstate) {
		mExpressionEvaluator = new ExpressionEvaluator<>();
		processExpression(rhs);

		assert mExpressionEvaluator.isFinished() : "Expression evaluator is not finished";
		assert mExpressionEvaluator.getRootEvaluator() != null : "There is no root evaluator";

		final List<IEvaluationResult<V>> results = mExpressionEvaluator.getRootEvaluator().evaluate(oldstate);

		if (results.isEmpty()) {
			throw new UnsupportedOperationException(
					"There is supposed to be at least on evaluation result for assignment expressions.");
		}

		final List<STATE> newStates = new ArrayList<>();
		for (final IEvaluationResult<V> res : results) {
			final Function<IProgramVarOrConst, STATE> varFunction = var -> oldstate.setValue(var, res.getValue());
			final Function<IProgramVarOrConst, STATE> boolFunction =
					var -> oldstate.setBooleanValue(var, res.getBooleanValue());

			final STATE newState = TypeUtils.applyVariableFunction(varFunction, boolFunction, null, lhsVar);

			newStates.add(newState);
		}
		return newStates;
	}

	private IProgramVarOrConst getLhsVariable(final LeftHandSide lhs) {
		assert mLhsVariable == null;
		processLeftHandSide(lhs);
		assert mLhsVariable != null : "processLeftHandSide(...) failed";
		final IProgramVarOrConst var = mLhsVariable;
		mLhsVariable = null;
		return var;
	}

	private void handleAssumeStatement(final AssumeStatement statement) {
		mExpressionEvaluator = new ExpressionEvaluator<>();

		final Expression formula = statement.getFormula();

		if (formula instanceof BooleanLiteral) {
			// handle the special case of a boolean literal
			final BooleanLiteral boolform = (BooleanLiteral) formula;
			if (!boolform.getValue()) {
				mReturnState.add(mOldState.bottomState());
			} else {
				mReturnState.add(mOldState);
			}
			return;
		}

		processExpression(formula);
		assert mExpressionEvaluator.isFinished();

		final List<IEvaluationResult<V>> result = mExpressionEvaluator.getRootEvaluator().evaluate(mOldState);

		for (final IEvaluationResult<V> res : result) {
			if (res.getValue().isBottom() || res.getBooleanValue() == BooleanValue.BOTTOM
					|| res.getBooleanValue() == BooleanValue.FALSE) {
				if (!mOldState.getVariables().isEmpty()) {
					mReturnState.add(mOldState.bottomState());
				}
			} else {
				// Assume statements must evaluate to true in all cases. Only the true part is important for succeeding
				// states. Otherwise, the return state will be bottom.
				final List<STATE> resultStates = mExpressionEvaluator.getRootEvaluator().inverseEvaluate(
						new NonrelationalEvaluationResult<>(res.getValue(), BooleanValue.TRUE), mOldState);
				mReturnState.addAll(resultStates);
			}
		}
	}

	private void handleHavocStatement(final HavocStatement statement) {
		STATE currentNewState = mOldState;

		for (final VariableLHS var : statement.getIdentifiers()) {
			final IProgramVarOrConst type = getBoogieVar(var);

			// TODO: Add array support.
			final STATE finalCurrentNewState = currentNewState;
			final Function<IProgramVarOrConst, STATE> varFunction =
					variable -> finalCurrentNewState.setValue(variable, finalCurrentNewState.createTopValue());
			final Function<IProgramVarOrConst, STATE> boolFunction =
					variable -> finalCurrentNewState.setBooleanValue(variable, BooleanValue.TOP);

			currentNewState = TypeUtils.applyVariableFunction(varFunction, boolFunction, null, type);
		}

		mReturnState.add(currentNewState);
	}

	@Override
	protected void visit(final VariableLHS lhs) {
		mLhsVariable = getBoogieVar(lhs);
	}

	@Override
	protected void visit(final IntegerLiteral expr) {
		final IEvaluator<V, STATE> evaluator =
				mEvaluatorFactory.createSingletonValueExpressionEvaluator(expr.getValue(), BigInteger.class);
		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final RealLiteral expr) {
		final IEvaluator<V, STATE> evaluator =
				mEvaluatorFactory.createSingletonValueExpressionEvaluator(expr.getValue(), BigDecimal.class);
		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final BinaryExpression expr) {
		final INAryEvaluator<V, STATE> evaluator =
				mEvaluatorFactory.createNAryExpressionEvaluator(2, EvaluatorUtils.getEvaluatorType(expr.getType()));
		evaluator.setOperator(expr.getOperator());
		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final FunctionApplication expr) {
		final IEvaluator<V, STATE> evaluator;
		final List<Declaration> decls = mSymbolTable.getFunctionOrProcedureDeclaration(expr.getIdentifier());

		// If we don't have a specification for the function, we return top.
		if (decls == null || decls.isEmpty()) {
			evaluator =
					mEvaluatorFactory.createSingletonValueTopEvaluator(EvaluatorUtils.getEvaluatorType(expr.getType()));
		} else {

			assert decls.get(0) instanceof FunctionDeclaration;

			final FunctionDeclaration fun = (FunctionDeclaration) decls.get(0);

			// If the body is empty (as in undefined), we return top.
			if (fun.getBody() == null) {
				evaluator = mEvaluatorFactory.createFunctionEvaluator(fun.getIdentifier(), fun.getInParams().length,
						EvaluatorUtils.getEvaluatorType(expr.getType()));
			} else {
				// TODO Handle bitshifts, bitwise and, bitwise or, etc.
				throw new UnsupportedOperationException(
						"The function application for not inlined functions is not yet supported.");
			}
		}

		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final IdentifierExpression expr) {
		final IEvaluator<V, STATE> evaluator =
				mEvaluatorFactory.createSingletonVariableExpressionEvaluator(getBoogieVar(expr));
		mExpressionEvaluator.addEvaluator(evaluator);
		super.visit(expr);
	}

	@Override
	protected void visit(final UnaryExpression expr) {
		final INAryEvaluator<V, STATE> evaluator =
				mEvaluatorFactory.createNAryExpressionEvaluator(1, EvaluatorUtils.getEvaluatorType(expr.getType()));
		evaluator.setOperator(expr.getOperator());
		mExpressionEvaluator.addEvaluator(evaluator);
		super.visit(expr);
	}

	@Override
	protected void visit(final BooleanLiteral expr) {
		final IEvaluator<V, STATE> evaluator = mEvaluatorFactory
				.createSingletonLogicalValueExpressionEvaluator(BooleanValue.getBooleanValue(expr.getValue()));
		mExpressionEvaluator.addEvaluator(evaluator);
	}

	@Override
	protected void visit(final ArrayStoreExpression expr) {
		throw new UnsupportedOperationException("Proper array handling is not implemented.");
	}

	@Override
	protected void visit(final ArrayAccessExpression expr) {
		throw new UnsupportedOperationException("Proper array handling is not implemented.");
	}

	@Override
	protected void visit(final IfThenElseExpression expr) {
		final IEvaluator<V, STATE> evaluator = mEvaluatorFactory.createConditionalEvaluator();
		mExpressionEvaluator.addEvaluator(evaluator);

		// Create a new expression for the negative case
		final UnaryExpression newUnary =
				new UnaryExpression(expr.getLocation(), UnaryExpression.Operator.LOGICNEG, expr.getCondition());

		// This expression should be added first to the evaluator inside the handling of processExpression.
		processExpression(newUnary);
	}

	private IProgramVarOrConst getBoogieVar(final VariableLHS expr) {
		IProgramVarOrConst rtr = mTemporaryVars.get(expr);
		if (rtr == null) {
			rtr = mBoogie2SmtSymbolTable.getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false);
		}
		if (rtr == null) {
			// hack for oldvars
			final String newIdent = expr.getIdentifier().replaceAll("old\\((.*)\\)", "$1");
			rtr = mBoogie2SmtSymbolTable.getBoogieVar(newIdent, expr.getDeclarationInformation(), false);
			rtr = ((BoogieNonOldVar) rtr).getOldVar();
		}
		assert rtr != null : "Could not find boogie var";
		return rtr;
	}

	private IProgramVarOrConst getBoogieVar(final IdentifierExpression expr) {
		IProgramVarOrConst returnVar =
				mBoogie2SmtSymbolTable.getBoogieVar(expr.getIdentifier(), expr.getDeclarationInformation(), false);

		if (returnVar != null) {
			if (mOldScope && returnVar instanceof IProgramNonOldVar) {
				return ((IProgramNonOldVar) returnVar).getOldVar();
			}
			return returnVar;
		}

		returnVar = mBoogie2SmtSymbolTable.getBoogieConst(expr.getIdentifier());
		assert returnVar != null;
		return returnVar;
	}

	@Override
	protected void visit(final BitvecLiteral expr) {
		throw new UnsupportedOperationException("Bit vector literals are not supported.");
	}

	@Override
	protected void visit(final BitVectorAccessExpression expr) {
		throw new UnsupportedOperationException("Bit vector access expressions are not supported.");
	}

	@Override
	protected void visit(final WildcardExpression expr) {
		throw new UnsupportedOperationException("Wildcard expressions are not supported.");
	}

	@Override
	protected void visit(final StructAccessExpression expr) {
		throw new UnsupportedOperationException("Struct access expressions are not supported.");
	}

	@Override
	protected void visit(final QuantifierExpression expr) {
		throw new UnsupportedOperationException("Quantifier expressions are not supported.");
	}
}
