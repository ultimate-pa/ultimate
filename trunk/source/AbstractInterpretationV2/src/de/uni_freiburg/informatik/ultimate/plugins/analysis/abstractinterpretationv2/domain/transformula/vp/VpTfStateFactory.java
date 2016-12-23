package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

public class VpTfStateFactory implements IVPFactory<VPTfState, VPNodeIdentifier, VPArrayIdentifier> {

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
				VPFactoryHelpers.addEquality(state.getNodeId(t1), state.getNodeId(t2), state, this);
		return result;
	}

	public Set<VPTfState> addDisequality(final Term t1, final Term t2, final VPTfState state) {
		return VPFactoryHelpers.addDisEquality(state.getNodeId(t1), state.getNodeId(t2), state, this);
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
				new VPArrayIdentifier(oldArray), 
				tfPreState.getNodeId(storeTerm),
				tfPreState.getNodeId(value),
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
		builder.setIsTop(state.isTop());

		for (final EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> egnInOldState : state.getAllEqGraphNodes()) {
			final VPNodeIdentifier nodeId = egnInOldState.nodeIdentifier;
			final EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> newGraphNode = builder.getEqGraphNode(nodeId);
			assert newGraphNode != null;
			EqGraphNode.copyFields(egnInOldState, newGraphNode, builder);
			assert !state.isTop() || newGraphNode.getRepresentative() == newGraphNode;
		}

		for (final VPDomainSymmetricPair<VPNodeIdentifier> pair : state.getDisEqualities()) {
			builder.addDisEquality(pair);
			assert !state.isTop() || pair.mFst.isLiteral()
					&& pair.mSnd.isLiteral() : "The only disequalites in a top state are between constants";
		}

		builder.addVars(new HashSet<>(state.getVariables()));


//		assert builder.mVars.equals(state.getVariables());
		return builder;
	}

	@Override
	public VPTfState getBottomState(final Set<IProgramVar> variables) {
		VPTfBottomState result = mVarsToBottomState.get(variables);
		if (result == null) {
			result = new VPTfBottomState(variables);
			mVarsToBottomState.put(variables, result);
		}
		return result;
	}

	/**
	 * Obtain the vanilla builder for the given TransFormula, make a (deep) copy of it
	 * and return it.
	 */
	@Override
	public VPTransitionStateBuilder createEmptyStateBuilder(final TransFormula tf) {
		 VPTransitionStateBuilder vanillaBuilder = mTfStatePreparer.getVPTfStateBuilder(tf);
		 assert vanillaBuilder.isTopConsistent();
		 
		 VPTransitionStateBuilder result = new VPTransitionStateBuilder(vanillaBuilder);
		 assert result.isTopConsistent();
		 return result;
	}


	/**
	 * Given a VPState and a TransFormula, this
	 *  - aquires the "vanilla" VPTfStateBuilder for the TransFormula
	 *  - collects everything that the state knows about the inVars of the TransFormula and updates the VPTfStateBuidler accordingly
	 * 
	 * @param state
	 * @param tf
	 * @return
	 */
	public VPTfState createTfState(final VPState<?> state, final UnmodifiableTransFormula tf) {
		if (isDebugMode()) {
			getLogger().debug("VPTfStateFactory: createTfState(..) (begin)");
		}

		if (state.isBottom()) {
			return getBottomState(state.getVariables());
		}

		if (state.isTop()) {
			final VPTransitionStateBuilder builder = createEmptyStateBuilder(tf);
			builder.addVariables(state.getVariables());
			return builder.build();
		}

		final VPTransitionStateBuilder builder = createEmptyStateBuilder(tf);
		builder.addVars(state.getVariables());
		
		Set<EqNode> inVarsAndConstantEqNodeSet = new HashSet<>();
		for (EqGraphNode<EqNode, IProgramVarOrConst> node : state.getAllEqGraphNodes()) {
			if (node.nodeIdentifier == null) {
				assert false;
				continue;
			}
			if (node.nodeIdentifier.isConstant()) {
				// we need to track all constants
				inVarsAndConstantEqNodeSet.add(node.nodeIdentifier);
				continue;
			}
			
			HashSet<IProgramVar> nodeVars = new HashSet<>(node.nodeIdentifier.getVariables());
			nodeVars.retainAll(tf.getOutVars().keySet());
			if (!nodeVars.isEmpty()) {
				// we need to track all nodes that talk about at least one invar
				inVarsAndConstantEqNodeSet.add(node.nodeIdentifier);
			}
		}
//		for (IProgramVar pv : tf.getInVars().keySet()) {
//			EqNode pvEqnode = mPreAnalysis.getEqNode(pv);
//			if (pvEqnode != null) {
//				inVarsAndConstantEqNodes.add(pvEqnode);
//			}
//		}
//		inVarsAndConstantEqNodes.addAll(mTfStatePreparer.getAllConstantEqNodes());
		
		List<EqNode> inVarsAndConstantEqNodes = new ArrayList<>(inVarsAndConstantEqNodeSet);

		for (int i = 0; i < inVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				EqNode inNode1 = inVarsAndConstantEqNodes.get(i);
				EqNode inNode2 = inVarsAndConstantEqNodes.get(j);

				if (inNode1 == inNode2) {
					// no need to disequate two identical nodes
					continue;
				}
				VPNodeIdentifier id1;
				VPNodeIdentifier id2;
				id1 = new VPNodeIdentifier(inNode1, 
						VPDomainHelpers.projectToVars(tf.getInVars(), inNode1.getVariables()),
						VPDomainHelpers.projectToVars(tf.getOutVars(), inNode1.getVariables()));
				id2 = new VPNodeIdentifier(inNode2, 
						VPDomainHelpers.projectToVars(tf.getInVars(), inNode2.getVariables()),
						VPDomainHelpers.projectToVars(tf.getOutVars(), inNode2.getVariables()));
		
				if (state.areUnEqual(inNode1, inNode2)) {
					builder.addDisEquality(id1, id2);
				}
			}
		}

		final VPTfState stateWithDisEqualitiesAdded = builder.build();

		Set<VPTfState> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);

		for (int i = 0; i < inVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				EqNode inNode1 = inVarsAndConstantEqNodes.get(i);
				EqNode inNode2 = inVarsAndConstantEqNodes.get(j);

				if (inNode1 == inNode2) {
					// no need to equate two identical nodes
					continue;
				}
				VPNodeIdentifier id1;
				VPNodeIdentifier id2;
				id1 = new VPNodeIdentifier(inNode1, 
						VPDomainHelpers.projectToVars(tf.getInVars(), inNode1.getVariables()),
						VPDomainHelpers.projectToVars(tf.getOutVars(), inNode1.getVariables()));
				id2 = new VPNodeIdentifier(inNode2, 
						VPDomainHelpers.projectToVars(tf.getInVars(), inNode2.getVariables()),
						VPDomainHelpers.projectToVars(tf.getOutVars(), inNode2.getVariables()));
				
				if (state.areEqual(inNode1, inNode2)) {
					resultStates = VPFactoryHelpers.addEquality(id1, id2, resultStates, this);
				}
			}
		}

		if (isDebugMode()) {
			getLogger().debug("VPTfStateFactory: createTfState(..) (end)");
		}
		assert resultStates.size() == 1 : "??";
		return resultStates.iterator().next();
	}

	@Override
	public Set<VPNodeIdentifier> getFunctionNodesForArray(final VPTfState tfState, final VPArrayIdentifier firstArray) {
		return tfState.getFunctionNodesForArray(firstArray);
	}
	
	@Override
	public ILogger getLogger() {
		return mPreAnalysis.getLogger();
	}

	@Override
	public boolean isDebugMode() {
		return mPreAnalysis.isDebugMode();
	}

	@Override
	public Benchmark getBenchmark() {
		return mPreAnalysis.getBenchmark();
	}
}
