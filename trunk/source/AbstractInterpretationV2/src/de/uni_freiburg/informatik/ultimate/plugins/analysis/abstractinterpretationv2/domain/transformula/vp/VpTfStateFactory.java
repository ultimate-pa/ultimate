package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.Collections;
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

public class VpTfStateFactory implements IVPFactory<VPTfState>{
	
	private final VPTransFormulaStateBuilderPreparer mTfStatePreparer;
	private final VPDomainPreanalysis mPreAnalysis;

	private final Map<Set<IProgramVar>, VPTfBottomState> mVarsToBottomState = new HashMap<>();

	public VpTfStateFactory(VPTransFormulaStateBuilderPreparer tfStatePreparer, VPDomainPreanalysis preAnalysis) {
		mTfStatePreparer = tfStatePreparer;
		mPreAnalysis = preAnalysis;
	}

	
	public Set<VPTfState> addEquality(Term t1, Term t2, VPTfState state) { 
		Set<VPTfState> result = VPFactoryHelpers.addEquality(
				new VPNodeIdentifier(t1), new VPNodeIdentifier(t2), state, this);
		return result;
	}
	
	public Set<VPTfState> addDisequality(Term t1, Term t2, VPTfState state) { 
		return VPFactoryHelpers.addDisEquality(
				new VPNodeIdentifier(t1), new VPNodeIdentifier(t2), state, this);
	}
	
	public Set<VPTfState> conjoin(VPTfState state1, VPTfState state2) {
		return VPFactoryHelpers.conjoin(state1, state2, this);
	}

	public VPTfState disjoin(VPTfState state1, VPTfState state2) {
		return VPFactoryHelpers.disjoin(state1, state2, this);
	}


	public Set<VPTfState> conjoinAll(List<Set<VPTfState>> andList) {
		return VPFactoryHelpers.conjoinAll(andList, this);
	}

	public Set<VPTfState> handleArrayEqualityWithException(TermVariable newArray, Term oldArray,
			ApplicationTerm storeTerm, Term value, VPTfState tfPreState) {
		return VPFactoryHelpers.arrayEqualityWithException(
				new VPArrayIdentifier(newArray), new VPArrayIdentifier(oldArray), 
				tfPreState.getEqGraphNode(storeTerm).nodeIdentifier,  //TODO: not nice
				tfPreState.getEqGraphNode(value).nodeIdentifier,  //TODO: not nice
				tfPreState, this);
	}


	public Set<VPTfState> handleArrayEquality(Term lhs, Term rhs, VPTfState tfPreState) {
		return VPFactoryHelpers.arrayEquality(
				new VPArrayIdentifier(lhs), new VPArrayIdentifier(rhs), tfPreState, this);
	}


	@Override
	public VPTransitionStateBuilder copy(VPTfState state) {
//		if (originalState.isBottom()) {
//			return new VPStateBottomBuilder(mDomain).setVars(originalState.getVariables());
//		}
		assert !state.isBottom();
		
		final VPTransitionStateBuilder builder = createEmptyStateBuilder(state.getTransFormula());
		
		for (EqGraphNode egnInOldState : state.getAllEqGraphNodes()) {
			VPNodeIdentifier nodeId = egnInOldState.nodeIdentifier;
			EqGraphNode newGraphNode = builder.getEqGraphNode(nodeId);
			EqGraphNode.copyFields(egnInOldState, newGraphNode, builder);
			assert !state.isTop() || newGraphNode.getRepresentative() == newGraphNode;
		}
		
		for (VPDomainSymmetricPair<VPNodeIdentifier> pair : state.getDisEqualities()) {
			builder.addDisEquality(pair);
			assert !state.isTop() || (pair.mFst.isLiteral() && pair.mSnd.isLiteral()) : 
				"The only disequalites in a top state are between constants";
		}
		
		builder.addVars(new HashSet<>(state.getVariables()));
		
		builder.setIsTop(state.isTop());

		assert builder.mVars.equals(state.getVariables());
		return builder;
	}


	@Override
	public VPTfState getBottomState(Set<IProgramVar> variables) {
		VPTfBottomState result = mVarsToBottomState.get(variables);
		if (result == null) {
			
		}
		return result;
	}


	@Override
	public VPTransitionStateBuilder createEmptyStateBuilder(TransFormula tf) {
		return mTfStatePreparer.getVPTfStateBuilder(tf);
	}


	public VPTfState createTfState(VPState state, UnmodifiableTransFormula tf) {
		if (state.isBottom()) {
			return getBottomState(state.getVariables());
		}
		
		if (state.isTop()) {
			VPTransitionStateBuilder builder = createEmptyStateBuilder(tf);
			builder.addVariables(state.getVariables());
			return builder.build();
		}
	
		
		IVPStateOrTfStateBuilder<VPTfState> builder = createEmptyStateBuilder(tf);
		builder.addVars(state.getVariables());
		builder.setIsTop(true);

		for (Entry<IProgramVar, TermVariable> inVar1 : tf.getInVars().entrySet()) {
			for (Entry<IProgramVar, TermVariable> inVar2 : tf.getInVars().entrySet()) {
				if (inVar1.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				VPNodeIdentifier id1 = new VPNodeIdentifier(inVar1.getValue());
				VPNodeIdentifier id2 = new VPNodeIdentifier(inVar2.getValue());
				if (state.areUnEqual(id1, id2)) {
					builder.addDisEquality(id1, id2);
					builder.setIsTop(false);
				}
			}
		}
		
		VPTfState stateWithDisEqualitiesAdded = builder.build();
		
		Set<VPTfState> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);
		
		for (Entry<IProgramVar, TermVariable> inVar1 : tf.getInVars().entrySet()) {
			for (Entry<IProgramVar, TermVariable> inVar2 : tf.getInVars().entrySet()) {
				if (inVar1.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				VPNodeIdentifier id1 = new VPNodeIdentifier(inVar1.getValue());
				VPNodeIdentifier id2 = new VPNodeIdentifier(inVar2.getValue());
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
	public Set<VPNodeIdentifier> getFunctionNodesForArray(VPTfState tfState, VPArrayIdentifier firstArray) {
		return tfState.getFunctionNodesForArray(firstArray);
	}	
}
