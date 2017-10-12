package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.array;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class ArrayDomainStatementProcessor<STATE extends IAbstractState<STATE>> {
	private final ArrayDomainExpressionProcessor<STATE> mExpressionProcessor;
	private final ArrayDomainToolkit<STATE> mToolkit;

	public ArrayDomainStatementProcessor(final ArrayDomainToolkit<STATE> toolkit) {
		mToolkit = toolkit;
		mExpressionProcessor = new ArrayDomainExpressionProcessor<>(toolkit);
	}

	public ArrayDomainState<STATE> process(final ArrayDomainState<STATE> state, final Statement statement) {
		if (statement instanceof AssignmentStatement) {
			return processAssignment(state, (AssignmentStatement) statement);
		} else if (statement instanceof AssumeStatement) {
			return processAssume(state, (AssumeStatement) statement);
		} else if (statement instanceof HavocStatement) {
			return processHavoc(state, (HavocStatement) statement);
		} else if (statement instanceof Label) {
			return state;
		}
		throw new UnsupportedOperationException("Unknonwn type of statement: " + statement);
	}

	private ArrayDomainState<STATE> processHavoc(final ArrayDomainState<STATE> state, final HavocStatement statement) {
		final List<IProgramVarOrConst> variables = Arrays.asList(statement.getIdentifiers()).stream()
				.map(mToolkit::getBoogieVar).collect(Collectors.toList());
		return state.removeVariables(variables).addVariables(variables);
	}

	private ArrayDomainState<STATE> processAssume(final ArrayDomainState<STATE> state,
			final AssumeStatement statement) {
		final Expression expression = statement.getFormula();
		final ExpressionResult<STATE> result = mExpressionProcessor.process(expression, state, true);
		final ArrayDomainState<STATE> resultingState = result.getState();
		final Collection<IProgramVarOrConst> auxVars = result.getAuxVars();
		return resultingState.removeVariables(auxVars);
	}

	private ArrayDomainState<STATE> processAssignment(final ArrayDomainState<STATE> state,
			final AssignmentStatement statement) {
		final LeftHandSide[] lhs = statement.getLhs();
		final Expression[] rhs = statement.getRhs();
		final int count = lhs.length;
		assert lhs.length == rhs.length && count > 0 : "Broken assignment statement";

		if (count > 1) {
			return processMultiAssignment(lhs, rhs, state);
		}
		// it is a single assignment
		return processSingleAssignment(lhs[0], rhs[0], state);
	}

	private ArrayDomainState<STATE> processMultiAssignment(final LeftHandSide[] lhs, final Expression[] rhs,
			final ArrayDomainState<STATE> state) {
		ArrayDomainState<STATE> returnState = state;
		for (int i = 0; i < lhs.length; i++) {
			final IProgramVarOrConst lhsVar = getLhsVariable(lhs[i]);
			final ArrayDomainState<STATE> unprojectedState = processSingleAssignment(lhs[i], rhs[i], state);
			final ArrayDomainState<STATE> projectedState = project(lhsVar, unprojectedState);
			returnState = returnState.patch(projectedState);
		}
		return returnState;
	}

	private ArrayDomainState<STATE> processSingleAssignment(final LeftHandSide lhs, final Expression rhs,
			final ArrayDomainState<STATE> oldstate) {
		final ExpressionResult<STATE> processed = mExpressionProcessor.process(rhs, oldstate, false);
		final Expression newExpr = processed.getExpression();
		if (lhs instanceof VariableLHS) {
			STATE newBoundState = oldstate.getSubState();
			final SegmentationMap newSegmentationMap = oldstate.getSegmentationMap();
			if (newExpr.getType() instanceof ArrayType) {
				if (newExpr instanceof IdentifierExpression) {
					final IProgramVarOrConst leftVar = mToolkit.getBoogieVar((VariableLHS) lhs);
					final IProgramVarOrConst rightVar = mToolkit.getBoogieVar((IdentifierExpression) newExpr);
					newSegmentationMap.move(leftVar, rightVar);
				} else if (newExpr instanceof ArrayStoreExpression) {
					final ArrayStoreExpression store = (ArrayStoreExpression) newExpr;
					// a:=b[i:=v] => a:=b; a[i]:=v
					final ArrayDomainState<STATE> tmpState = processSingleAssignment(lhs, store.getArray(), oldstate);
					final ArrayLHS arrayLhs = new ArrayLHS(null, lhs, store.getIndices());
					return processSingleAssignment(arrayLhs, store.getValue(), tmpState);
				} else {
					throw new UnsupportedOperationException(
							"The domain does not support array-expressions except identifier and store");
				}
			} else {
				final AssignmentStatement assignment = constructSingleAssignment(lhs, newExpr);
				newBoundState = mToolkit.handleStatementBySubdomain(oldstate.getSubState(), assignment);
			}
			return oldstate.updateState(newBoundState, newSegmentationMap).removeUnusedAuxVars();
		} else if (lhs instanceof ArrayLHS) {
			return processArrayAssignment((ArrayLHS) lhs, rhs, oldstate);
		}
		throw new UnsupportedOperationException("Unkonwn type of " + lhs);
	}

	private ArrayDomainState<STATE> processArrayAssignment(final ArrayLHS lhs, final Expression rhs,
			final ArrayDomainState<STATE> oldstate) {
		// TODO: a[i]:=v
		return null;
	}

	private AssignmentStatement constructSingleAssignment(final LeftHandSide lhs, final Expression rhs) {
		return new AssignmentStatement(null, new LeftHandSide[] { lhs }, new Expression[] { rhs });
	}

	private IProgramVarOrConst getLhsVariable(final LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			return mToolkit.getBoogieVar((VariableLHS) lhs);
		} else if (lhs instanceof ArrayLHS) {
			return getLhsVariable(((ArrayLHS) lhs).getArray());
		}
		throw new UnsupportedOperationException("Unkonwn type of " + lhs);
	}

	private ArrayDomainState<STATE> project(final IProgramVarOrConst lhsVar, final ArrayDomainState<STATE> state) {
		final Set<IProgramVarOrConst> varsToRemove = new HashSet<>(state.getVariables());
		varsToRemove.remove(lhsVar);
		return state.removeVariables(varsToRemove);
	}
}
