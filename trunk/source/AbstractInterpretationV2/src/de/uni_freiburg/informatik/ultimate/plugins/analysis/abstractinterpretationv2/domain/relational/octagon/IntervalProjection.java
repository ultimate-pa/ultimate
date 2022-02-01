/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.boogie.IBoogieSymbolTableVariableProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;

/**
 * Utilities to project octagons to intervals, calculated expression using intervals, and assigning the resulting
 * intervals to octagons.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class IntervalProjection {

	private final IBoogieSymbolTableVariableProvider mBpl2smtSymbolTable;

	public IntervalProjection(final IBoogieSymbolTableVariableProvider iBoogieSymbolTableVariableProvider) {
		mBpl2smtSymbolTable = iBoogieSymbolTableVariableProvider;
	}

	/**
	 * Processes an assignment by projection to intervals.
	 *
	 * @param var
	 *            Variable to be assigned.
	 * @param rhs
	 *            Expression without if-expressions, describing te new value of the variable.
	 * @param oldStates
	 *            Octagon abstract states to be updated -- will be modified in-place.
	 * @return Updated states in the same list.
	 */
	public List<OctDomainState> assignNumericVarWithoutIfs(final IProgramVarOrConst var, final Expression rhs,
			List<OctDomainState> oldStates) {

		oldStates = OctPostOperator.removeBottomStates(oldStates);
		for (final OctDomainState state : oldStates) {
			final IntervalDomainValue interval = projectNumericExprWithoutIfs(rhs, state);
			state.assignNumericVarInterval(var, new OctInterval(interval));
		}
		return oldStates;
	}

	/**
	 * Processes an assignment by projection to intervals.
	 *
	 * @param var
	 *            Variable to be assigned.
	 * @param rhs
	 *            Affine expression, describing te new value of the variable.
	 * @param oldStates
	 *            Octagon abstract states to be updated -- will be modified in-place.
	 * @return Updated states in the same list.
	 */
	public List<OctDomainState> assignNumericVarAffine(final IProgramVarOrConst var, final AffineExpression rhs,
			List<OctDomainState> oldStates) {

		oldStates = OctPostOperator.removeBottomStates(oldStates);
		for (final OctDomainState state : oldStates) {
			final IntervalDomainValue interval = projectAffineExpr(rhs, state);
			state.assignNumericVarInterval(var, new OctInterval(interval));
		}
		return oldStates;
	}

	/**
	 * Project an octagon to intervals and calculate the abstract result (interval) of an expression.
	 *
	 * @param expr
	 *            Expression to be evaluated.
	 * @param state
	 *            Octagon abstract state, describing the values variables can have.
	 * @return Abstract result (interval) of the expression
	 */
	public IntervalDomainValue projectNumericExprWithoutIfs(final Expression expr, final OctDomainState state) {
		// TODO (?) cache interval projections of each variable

		if (expr instanceof IntegerLiteral) {
			final IntervalValue pointInterval = new IntervalValue(((IntegerLiteral) expr).getValue());
			return new IntervalDomainValue(pointInterval, pointInterval);

		} else if (expr instanceof RealLiteral) {
			final IntervalValue pointInterval = new IntervalValue(((RealLiteral) expr).getValue());
			return new IntervalDomainValue(pointInterval, pointInterval);

		} else if (expr instanceof IdentifierExpression) {
			final IdentifierExpression iexpr = ((IdentifierExpression) expr);
			final IProgramVar var =
					mBpl2smtSymbolTable.getBoogieVar(iexpr.getIdentifier(), iexpr.getDeclarationInformation(), false);
			assert var != null;
			final OctInterval octInterval = state.projectToInterval(var);
			return octInterval.toIvlInterval();

		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression unExpr = (UnaryExpression) expr;
			switch (unExpr.getOperator()) {
			case ARITHNEGATIVE:
				return projectNumericExprWithoutIfs(unExpr.getExpr(), state).negate();
			default:
				// see end of this method
			}

		} else if (expr instanceof BinaryExpression) {
			final BinaryExpression binExpr = (BinaryExpression) expr;
			final IntervalDomainValue left = projectNumericExprWithoutIfs(binExpr.getLeft(), state);
			final IntervalDomainValue right = projectNumericExprWithoutIfs(binExpr.getRight(), state);
			switch (binExpr.getOperator()) {
			case ARITHPLUS:
				return left.add(right);
			case ARITHMINUS:
				return left.subtract(right);
			case ARITHMUL:
				return left.multiply(right);
			case ARITHDIV:
				if (TypeUtils.isNumericInt(binExpr.getType())) {
					return left.divideInteger(right);
				}
				return left.divideReal(right);
			case ARITHMOD:
				assert TypeUtils.isNumericInt(binExpr.getType());
				return left.modulo(right);
			default:
				// see end of this method
			}

		}
		return new IntervalDomainValue(); // \top = safe over-approximation
	}

	/**
	 * Project an octagon to intervals and calculate the abstract result (interval) of an affine expression.
	 *
	 * @param expr
	 *            Affine expression to be evaluated.
	 * @param state
	 *            Octagon abstract state, describing the values variables can have.
	 * @return Abstract result (interval) of the expression
	 */
	public IntervalDomainValue projectAffineExpr(final AffineExpression expr, final OctDomainState state) {
		IntervalDomainValue resultInterval = new IntervalDomainValue(0, 0);
		for (final Entry<IProgramVarOrConst, BigDecimal> summand : expr.getCoefficients().entrySet()) {
			final IntervalDomainValue varValue = state.projectToInterval(summand.getKey()).toIvlInterval();
			final IntervalValue factor = new IntervalValue(summand.getValue());
			resultInterval = resultInterval.add(varValue.multiply(new IntervalDomainValue(factor, factor)));
		}
		final IntervalValue constant = new IntervalValue(expr.getConstant());
		resultInterval = resultInterval.add(new IntervalDomainValue(constant, constant));
		return resultInterval;
	}

	/**
	 * Project an octagon to intervals and returns a new {@link IntervalDomainState}.
	 *
	 * @param state
	 *            The given octagon state.
	 * @return A new {@link IntervalDomainState} representing the projection of the octagon to intervals.
	 */
	protected static IntervalDomainState projectOctagonStateToIntervalDomainState(final ILogger logger,
			final OctDomainState state) {
		final Set<IProgramVarOrConst> variables = state.getVariables();
		final Map<IProgramVarOrConst, IntervalDomainValue> numericValuesMap = new HashMap<>();
		final Map<IProgramVarOrConst, BooleanValue> booleanValuesMap = new HashMap<>();

		for (final IProgramVarOrConst var : variables) {
			final Sort realSort = var.getSort().getRealSort();

			if (SmtSortUtils.isNumericSort(realSort)) {
				final IntervalDomainValue interval = state.projectToInterval(var).toIvlInterval();
				numericValuesMap.put(var, interval);
			} else if (SmtSortUtils.isBoolSort(realSort)) {
				final BoolValue bool = state.getBoolValue(var);
				BooleanValue boolValue;
				switch (bool) {
				case BOT:
					boolValue = BooleanValue.BOTTOM;
					break;
				case FALSE:
					boolValue = BooleanValue.FALSE;
					break;
				case TOP:
					boolValue = BooleanValue.TOP;
					break;
				case TRUE:
					boolValue = BooleanValue.TRUE;
					break;
				default:
					throw new UnsupportedOperationException("Unsupported boolean value: " + bool);
				}
				booleanValuesMap.put(var, boolValue);
			} else if (SmtSortUtils.isArraySort(realSort)) {
				numericValuesMap.put(var, new IntervalDomainValue());
			} else {
				throw new UnsupportedOperationException("Unsupported sort: " + var.getSort());
			}
		}

		return new IntervalDomainState(logger, variables, numericValuesMap, booleanValuesMap, state.isBottom());
	}

	/**
	 * Projects the given {@link IntervalDomainState} to the given {@link OctDomainState}.
	 *
	 * @param logger
	 *            The logger.
	 * @param state
	 *            The {@link IntervalDomainState} to apply to the {@link OctDomainState}.
	 * @param previousOctState
	 *            The {@link OctDomainState}.
	 * @param restrictedVars
	 *            If not null, only the variables specified here will be updated in the previous state.
	 * @param octDomainStateFactory
	 */
	protected static OctDomainState projectIntervalStateToOctagon(final ILogger logger, final IntervalDomainState state,
			final OctDomainState previousOctState, final Set<IProgramVarOrConst> restrictedVars) {

		if (state.isBottom()) {
			return previousOctState.createFreshBottomState();
		}

		final Set<IProgramVarOrConst> variables = state.getVariables();
		final OctDomainState newState = previousOctState.deepCopy();

		for (final IProgramVarOrConst var : variables) {
			if (restrictedVars != null && !restrictedVars.contains(var)) {
				continue;
			}

			final Sort realSort = var.getSort().getRealSort();

			if (SmtSortUtils.isNumericSort(realSort)) {
				final IntervalDomainValue interval = state.getValue(var);
				newState.assignNumericVarInterval(var, new OctInterval(interval));
			} else if (SmtSortUtils.isBoolSort(realSort)) {
				final BooleanValue bool = state.getBooleanValue(var);
				BoolValue boolValue;
				switch (bool) {
				case BOTTOM:
					boolValue = BoolValue.BOT;
					break;
				case FALSE:
					boolValue = BoolValue.FALSE;
					break;
				case TOP:
					boolValue = BoolValue.TOP;
					break;
				case TRUE:
					boolValue = BoolValue.TRUE;
					break;
				default:
					throw new UnsupportedOperationException("Unsupported bool value: " + bool);
				}
				newState.assignBooleanVar(var, boolValue);
			} else if (SmtSortUtils.isArraySort(realSort)) {
				// TODO Handle proper array handling.
				// Do nothing here, leave the value as it is.
			} else {
				throw new UnsupportedOperationException("Unsupported sort: " + realSort);
			}
		}
		return newState;
	}
}
