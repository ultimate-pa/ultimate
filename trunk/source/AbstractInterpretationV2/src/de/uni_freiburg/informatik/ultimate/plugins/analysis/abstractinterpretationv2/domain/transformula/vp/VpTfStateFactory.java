package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class VpTfStateFactory implements IVPFactory<VPTfState> {

	private final VPTransFormulaStateBuilderPreparer mTfStatePreparer;
	private final VPDomainPreanalysis mPreAnalysis;

	private final Map<Set<IProgramVar>, VPTfBottomState> mVarsToBottomState = new HashMap<>();

	public VpTfStateFactory(final VPTransFormulaStateBuilderPreparer tfStatePreparer,
			final VPDomainPreanalysis preAnalysis) {
		mTfStatePreparer = tfStatePreparer;
		mPreAnalysis = preAnalysis;
	}

	public Set<VPTfState> addEquality(final Term t1, final Term t2, final VPTfState state) {
		final Set<VPTfState> result =
				VPFactoryHelpers.addEquality(new VPNodeIdentifier(t1), new VPNodeIdentifier(t2), state, this);
		return result;
	}

	public Set<VPTfState> addDisequality(final Term t1, final Term t2, final VPTfState state) {
		return VPFactoryHelpers.addDisEquality(new VPNodeIdentifier(t1), new VPNodeIdentifier(t2), state, this);
	}

	public Set<VPTfState> conjoin(final VPTfState state1, final VPTfState state2) {
		return VPFactoryHelpers.conjoin(state1, state2, this);
	}

	public VPTfState disjoin(final VPTfState state1, final VPTfState state2) {
		return VPFactoryHelpers.disjoin(state1, state2, this);
	}

	public Set<VPTfState> conjoinAll(final List<Set<VPTfState>> andList) {
		return VPFactoryHelpers.conjoinAll(andList, this);
	}

	public Set<VPTfState> handleArrayEqualityWithException(final TermVariable newArray, final Term oldArray,
			final ApplicationTerm storeTerm, final Term value, final VPTfState tfPreState) {
		return VPFactoryHelpers.arrayEqualityWithException(new VPArrayIdentifier(newArray),
				new VPArrayIdentifier(oldArray), tfPreState.getEqGraphNode(storeTerm).nodeIdentifier, // TODO: not nice
				tfPreState.getEqGraphNode(value).nodeIdentifier, // TODO: not nice
				tfPreState, this);
	}

	public Set<VPTfState> handleArrayEquality(final Term lhs, final Term rhs, final VPTfState tfPreState) {
		return VPFactoryHelpers.arrayEquality(new VPArrayIdentifier(lhs), new VPArrayIdentifier(rhs), tfPreState, this);
	}

	@Override
	public VPTransitionStateBuilder copy(final VPTfState state) {
		// if (originalState.isBottom()) {
		// return new VPStateBottomBuilder(mDomain).setVars(originalState.getVariables());
		// }
		assert !state.isBottom();

		final VPTransitionStateBuilder builder = createEmptyStateBuilder(state.getTransFormula());

		for (final EqGraphNode egnInOldState : state.getAllEqGraphNodes()) {
			final VPNodeIdentifier nodeId = egnInOldState.nodeIdentifier;
			final EqGraphNode newGraphNode = builder.getEqGraphNode(nodeId);
			EqGraphNode.copyFields(egnInOldState, newGraphNode, builder);
			assert !state.isTop() || newGraphNode.getRepresentative() == newGraphNode;
		}

		for (final VPDomainSymmetricPair<VPNodeIdentifier> pair : state.getDisEqualities()) {
			builder.addDisEquality(pair);
			assert !state.isTop() || pair.mFst.isLiteral()
					&& pair.mSnd.isLiteral() : "The only disequalites in a top state are between constants";
		}

		builder.addVars(new HashSet<>(state.getVariables()));

		builder.setIsTop(state.isTop());

		assert builder.mVars.equals(state.getVariables());
		return builder;
	}

	@Override
	public VPTfState getBottomState(final Set<IProgramVar> variables) {
		final VPTfBottomState result = mVarsToBottomState.get(variables);
		if (result == null) {

		}
		return result;
	}

	@Override
	public VPTransitionStateBuilder createEmptyStateBuilder(final TransFormula tf) {
		return mTfStatePreparer.getVPTfStateBuilder(tf);
	}

	public VPTfState createTfState(final VPState<?> state, final UnmodifiableTransFormula tf) {
		if (state.isBottom()) {
			return getBottomState(state.getVariables());
		}

		if (state.isTop()) {
			final VPTransitionStateBuilder builder = createEmptyStateBuilder(tf);
			builder.addVariables(state.getVariables());
			return builder.build();
		}

		final IVPStateOrTfStateBuilder<VPTfState> builder = createEmptyStateBuilder(tf);
		builder.addVars(state.getVariables());
		builder.setIsTop(true);

		for (final Entry<IProgramVar, TermVariable> inVar1 : tf.getInVars().entrySet()) {
			for (final Entry<IProgramVar, TermVariable> inVar2 : tf.getInVars().entrySet()) {
				if (inVar1.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				final VPNodeIdentifier id1 = new VPNodeIdentifier(inVar1.getValue());
				final VPNodeIdentifier id2 = new VPNodeIdentifier(inVar2.getValue());
				if (state.areUnEqual(id1, id2)) {
					builder.addDisEquality(id1, id2);
					builder.setIsTop(false);
				}
			}
		}

		final VPTfState stateWithDisEqualitiesAdded = builder.build();

		Set<VPTfState> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);

		for (final Entry<IProgramVar, TermVariable> inVar1 : tf.getInVars().entrySet()) {
			for (final Entry<IProgramVar, TermVariable> inVar2 : tf.getInVars().entrySet()) {
				if (inVar1.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				final VPNodeIdentifier id1 = new VPNodeIdentifier(inVar1.getValue());
				final VPNodeIdentifier id2 = new VPNodeIdentifier(inVar2.getValue());
				if (state.areEqual(id1, id2)) {
					resultStates = VPFactoryHelpers.addEquality(id1, id2, resultStates, this);
					builder.setIsTop(false);
				}
			}
		}

		assert resultStates.size() == 1 : "??";
		return resultStates.iterator().next();
	}

	@Override
	public Set<VPNodeIdentifier> getFunctionNodesForArray(final VPTfState tfState, final VPArrayIdentifier firstArray) {
		return tfState.getFunctionNodesForArray(firstArray);
	}
}
