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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.typeutils.TypeUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class OctStatementProcessor {

	private final OctPostOperator mPostOp;
	private final IntervalProjection mIntervalProjection;

	public OctStatementProcessor(final OctPostOperator postOperator) {
		mPostOp = postOperator;
		mIntervalProjection = new IntervalProjection(mPostOp.getBoogie2SmtSymbolTable());
	}

	public List<OctDomainState> processStatement(final Statement statement, final List<OctDomainState> oldStates) {
		if (statement instanceof AssignmentStatement) {
			return processAssignmentStatement((AssignmentStatement) statement, oldStates);
		} else if (statement instanceof AssumeStatement) {
			final Expression assumption = ((AssumeStatement) statement).getFormula();
			return mPostOp.getAssumeProcessor().assume(assumption, oldStates);
		} else if (statement instanceof HavocStatement) {
			return processHavocStatement((HavocStatement) statement, oldStates);
		}
		if (statement instanceof Label) {
			return oldStates; // nothing to do
		}
		throw new UnsupportedOperationException("Unsupported type of statement: " + statement);
	}

	private List<OctDomainState> processAssignmentStatement(final AssignmentStatement statement,
			final List<OctDomainState> oldStates) {

		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();
		assert lhs.length == rhs.length : "Unbalanced assignment: " + statement;
		final int length = lhs.length;
		if (length == 1) {
			final LeftHandSide l = lhs[0];
			if (l instanceof VariableLHS) {
				return processSingleAssignment(mPostOp.getBoogieVar((VariableLHS) l), rhs[0], oldStates);
			}
			// variables of unsupported types (e.g. arrays) are assumed to be \top all the time
			return oldStates;
		}

		final Map<String, IProgramVarOrConst> tmpVars = new HashMap<>();
		final List<Pair<IProgramVar, Expression>> mapLhsToRhs = new ArrayList<>(length);
		final List<Pair<IProgramVarOrConst, IProgramVarOrConst>> mapOrigVarToTmpVar = new ArrayList<>(length);
		for (int i = 0; i < length; ++i) {
			final LeftHandSide l = lhs[i];

			if (l instanceof VariableLHS) {
				final VariableLHS vLhs = (VariableLHS) l;
				final IProgramVar origVar = mPostOp.getBoogieVar(vLhs);
				// unique (origVar is unique + braces are not allowed)
				final String tmpVarName = "octTmp(" + origVar + ")";
				final IProgramVar tmpVar = AbsIntUtil.createTemporaryIBoogieVar(tmpVarName, vLhs.getType());

				tmpVars.put(tmpVarName, tmpVar);
				mapLhsToRhs.add(new Pair<>(tmpVar, rhs[i]));
				mapOrigVarToTmpVar.add(new Pair<>(origVar, tmpVar));
			}
			// else: variables of unsupported types are assumed to be \top all the time
		}

		// add temporary variables
		List<OctDomainState> tmpStates = new ArrayList<>(oldStates.size());
		for (final OctDomainState oldState : oldStates) {
			tmpStates.add(oldState.addVariables(tmpVars.values()));
		}

		// (tmpVar := origExpr)*
		// note: oldStates may be modified, since addVariables() returns only a shallow copy. Not a problem.
		for (final Pair<IProgramVar, Expression> assignment : mapLhsToRhs) {
			tmpStates = processSingleAssignment(assignment.getFirst(), assignment.getSecond(), tmpStates);
		}

		// (origVar := tmpVar)*
		tmpStates = OctPostOperator.removeBottomStates(tmpStates); // important!
		tmpStates.forEach(tmpState -> tmpState.copyVars(mapOrigVarToTmpVar));

		// remove temporary variables
		final List<OctDomainState> newStates = new ArrayList<>(oldStates.size());
		tmpStates.forEach(tmpState -> newStates.add(tmpState.removeVariables(tmpVars.values())));
		return newStates;
	}

	public List<OctDomainState> processSingleAssignment(final IProgramVarOrConst targetVar, final Expression rhs,
			final List<OctDomainState> oldStates) {
		final IBoogieType type = rhs.getType();
		if (TypeUtils.isBoolean(type)) {
			return processBooleanAssign(targetVar, rhs, oldStates);
		} else if (TypeUtils.isNumeric(type)) {
			return processNumericAssign(targetVar, rhs, oldStates);
		} else {
			return oldStates; // variables of unsupported types are assumed to be \top all the time
		}
	}

	private List<OctDomainState> processBooleanAssign(final IProgramVarOrConst targetVar, final Expression rhs,
			List<OctDomainState> oldStates) {

		if (rhs instanceof BooleanLiteral) {
			final BoolValue value = BoolValue.get(((BooleanLiteral) rhs).getValue());
			oldStates = OctPostOperator.removeBottomStates(oldStates); // important!
			oldStates.forEach(s -> s.assignBooleanVar(targetVar, value));
			return oldStates;

		} else if (rhs instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) rhs;
			oldStates = OctPostOperator.removeBottomStates(oldStates); // important!
			if (AbsIntUtil.isVariable(ie)) {
				final IProgramVarOrConst sourceVar = mPostOp.getBoogieVar(ie);
				oldStates.forEach(s -> s.copyVar(targetVar, sourceVar));
			} else {
				oldStates.forEach(s -> s.havocVar(targetVar));
			}
			return oldStates;

		} else {
			final Expression notRhs = mPostOp.getExprTransformer().logicNegCached(rhs);
			return mPostOp.splitF(oldStates, stateList -> {
				stateList = mPostOp.getAssumeProcessor().assume(rhs, stateList);
				stateList = OctPostOperator.removeBottomStates(stateList); // important!
				stateList.forEach(state -> state.assignBooleanVar(targetVar, BoolValue.TRUE));
				return stateList;
			}, stateList -> {
				stateList = mPostOp.getAssumeProcessor().assume(notRhs, stateList);
				stateList = OctPostOperator.removeBottomStates(stateList); // important!
				stateList.forEach(state -> state.assignBooleanVar(targetVar, BoolValue.FALSE));
				return stateList;
			});
		}
	}

	private List<OctDomainState> processNumericAssign(final IProgramVarOrConst targetVar, final Expression rhs,
			final List<OctDomainState> oldStates) {

		final List<OctDomainState> newStates = new ArrayList<>();
		final IfExpressionTree ifExprTree = mPostOp.getExprTransformer().removeIfExprsCached(rhs);
		for (final Pair<Expression, List<OctDomainState>> leaf : ifExprTree.assumeLeafs(mPostOp, oldStates)) {
			List<OctDomainState> oldStatesIfsAssumed = leaf.getSecond();
			oldStatesIfsAssumed = OctPostOperator.removeBottomStates(oldStatesIfsAssumed); // important!
			newStates.addAll(processNumericAssignWithoutIfs(targetVar, leaf.getFirst(), oldStatesIfsAssumed));
		}
		return mPostOp.joinDownToMax(newStates);
	}

	private List<OctDomainState> processNumericAssignWithoutIfs(final IProgramVarOrConst targetVar,
			final Expression rhs, final List<OctDomainState> oldStates) {

		final AffineExpression ae = mPostOp.getExprTransformer().affineExprCached(rhs);
		if (ae != null) {
			AffineExpression.OneVarForm ovf;
			AffineExpression.TwoVarForm tvf;
			if (ae.isConstant()) {
				final OctValue value = new OctValue(ae.getConstant());
				oldStates.forEach(s -> s.assignNumericVarConstant(targetVar, value));
				return oldStates;
			} else if ((ovf = ae.getOneVarForm()) != null) {
				Consumer<OctDomainState> action = s -> s.copyVar(targetVar, ovf.var);
				if (ovf.negVar) {
					action = action.andThen(s -> s.negateNumericVar(targetVar));
				}
				if (ovf.constant.signum() != 0) {
					action = action.andThen(s -> s.incrementNumericVar(targetVar, ovf.constant));
				}
				oldStates.forEach(action);
				return oldStates;
			} else if ((tvf = ae.getTwoVarForm()) != null) {
				for (final OctDomainState oldState : oldStates) {
					final OctInterval oi = oldState.projectToInterval(tvf);
					oldState.assignNumericVarInterval(targetVar, oi);
				}
				return oldStates;
			} else if (mPostOp.isFallbackAssignIntervalProjectionEnabled()) {

				return mIntervalProjection.assignNumericVarAffine(targetVar, ae, oldStates);
			}
		} else if (mPostOp.isFallbackAssignIntervalProjectionEnabled()) { // no affine form found
			return mIntervalProjection.assignNumericVarWithoutIfs(targetVar, rhs, oldStates);
		}

		// could not interpret rhs -- return safe over-approximation (targetVar := \top)
		oldStates.forEach(s -> s.havocVar(targetVar));
		return oldStates;
	}

	private List<OctDomainState> processHavocStatement(final HavocStatement statement, List<OctDomainState> oldStates) {
		final List<IProgramVarOrConst> vars = new ArrayList<>();
		for (final VariableLHS lhs : statement.getIdentifiers()) {
			vars.add(mPostOp.getBoogieVar(lhs));
		}
		oldStates = OctPostOperator.removeBottomStates(oldStates); // important!
		oldStates.forEach(s -> s.havocVars(vars));
		return oldStates;
	}
}
