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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.AbsIntBenchmark;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.Evaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.ExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluatorFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.CrossProducts;

/**
 * Processes Boogie {@link Statement}s and returns a new {@link IntervalDomainState} for the given statement.
 *
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class NonrelationalStatementProcessor<STATE extends NonrelationalState<STATE, V>, V extends INonrelationalValue<V>>
		extends BoogieVisitor {

	private final IBoogieSymbolTableVariableProvider mBoogie2SmtSymbolTable;
	private final ILogger mLogger;

	private STATE mOldState;
	private List<STATE> mReturnState;
	private IProgramVarOrConst mLhsVariable;
	private Map<LeftHandSide, IProgramVarOrConst> mTemporaryVars;

	private AbsIntBenchmark<IcfgEdge> mAbsIntBenchmark;
	private final NonrelationalEvaluator<STATE, V> mEvaluator;

	public NonrelationalStatementProcessor(final ILogger logger, final IBoogieSymbolTableVariableProvider bpl2SmtTable,
			final NonrelationalEvaluator<STATE, V> evaluator) {
		mBoogie2SmtSymbolTable = bpl2SmtTable;
		mLogger = logger;
		mEvaluator = evaluator;
		mLhsVariable = null;
	}

	/**
	 * Computes the abstract post states for a given statement and prestate.
	 *
	 * @param oldState
	 *            The prestate to use.
	 * @param statement
	 *            The statement to compute the abstract post states for.
	 * @param absIntBenchmark
	 *            An instance of {@link AbsIntBenchmark} which is used by the processor to report benchmarks. This
	 *            parameter may be null, if no benchmarks should be collected.
	 * @return
	 */
	public List<STATE> process(final STATE oldState, final Statement statement,
			final AbsIntBenchmark<IcfgEdge> absIntBenchmark) {
		return process(oldState, statement, Collections.emptyMap(), absIntBenchmark);
	}

	/**
	 * Computes the abstract post states for a given statement and prestate.
	 *
	 * @param oldState
	 *            The prestate to use.
	 * @param statement
	 *            The statement to compute the abstract post states for.
	 * @param tmpVars
	 *            A map of left hand side variables to program variables that have been temporarily added to the states.
	 *            This map is needed for the computation of the abstract post states when dealing with transformulas.
	 * @param absIntBenchmark
	 *            An instance of {@link AbsIntBenchmark} which is used by the processor to report benchmarks. This
	 *            parameter may be null, if no benchmarks should be collected.
	 * @return
	 */
	public List<STATE> process(final STATE oldState, final Statement statement,
			final Map<LeftHandSide, IProgramVarOrConst> tmpVars, final AbsIntBenchmark<IcfgEdge> absIntBenchmark) {
		assert oldState != null;
		assert statement != null;
		assert tmpVars != null;

		mReturnState = new ArrayList<>();
		mOldState = oldState;
		mTemporaryVars = tmpVars;
		mLhsVariable = null;

		mAbsIntBenchmark = absIntBenchmark;

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
		final Collection<IEvaluationResult<V>> results = mEvaluator.evaluate(oldstate, rhs);

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

		if (mAbsIntBenchmark != null) {
			final Evaluator<V, STATE> evaluator = mEvaluator.createEvaluator(rhs);
			mAbsIntBenchmark.recordEvaluationRecursionDepth(evaluator.getEvaluationRecursionDepth());
			mAbsIntBenchmark.recordInverseEvaluationRecursionDepth(evaluator.getInverseEvaluationRecursionDepth());
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
		final Expression formula = statement.getFormula();
		if (formula instanceof BooleanLiteral) {
			// handle the special case of a boolean literal
			final BooleanLiteral boolform = (BooleanLiteral) formula;
			if (!boolform.getValue()) {
				if (!mOldState.getVariables().isEmpty()) {
					mReturnState.add(mOldState.bottomState());
				}
			} else {
				mReturnState.add(mOldState);
			}
			return;
		}

		final Evaluator<V, STATE> evaluator = mEvaluator.createEvaluator(formula);
		final Collection<IEvaluationResult<V>> results = mEvaluator.evaluate(mOldState, formula);

		for (final IEvaluationResult<V> res : results) {
			if (res.getValue().isBottom() || res.getBooleanValue() == BooleanValue.BOTTOM
					|| res.getBooleanValue() == BooleanValue.FALSE) {
				if (!mOldState.getVariables().isEmpty()) {
					mReturnState.add(mOldState.bottomState());
				}
			} else {
				// Assume statements must evaluate to true in all cases. Only the true part is important for succeeding
				// states. Otherwise, the return state will be bottom.
				final Collection<STATE> resultStates = evaluator.inverseEvaluate(
						new NonrelationalEvaluationResult<>(res.getValue(), BooleanValue.TRUE), mOldState, 0);
				mReturnState.addAll(
						resultStates.stream().map(state -> state.intersect(mOldState)).collect(Collectors.toList()));
			}
		}

		if (mAbsIntBenchmark != null) {
			mAbsIntBenchmark.recordEvaluationRecursionDepth(evaluator.getEvaluationRecursionDepth());
			mAbsIntBenchmark.recordInverseEvaluationRecursionDepth(evaluator.getInverseEvaluationRecursionDepth());
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
}
