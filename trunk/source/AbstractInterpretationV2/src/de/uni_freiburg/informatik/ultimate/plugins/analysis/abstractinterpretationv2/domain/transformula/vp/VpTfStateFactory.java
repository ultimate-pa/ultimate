/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
	 *  - collects everything that the state knows about the inVars of the TransFormula and updates the VPTfStateBuidler 
	 *    accordingly
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
		
		Set<EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> inVarsAndConstantEqNodeSet = new HashSet<>();
		for (EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> node : builder.getAllEqGraphNodes()) {
			if (node.nodeIdentifier.isInOrThrough()) {
				
			}
		}
		
		List<EqGraphNode<VPNodeIdentifier, VPArrayIdentifier>> inVarsAndConstantEqNodes = new ArrayList<>(inVarsAndConstantEqNodeSet);

		for (int i = 0; i < inVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> inNode1 = inVarsAndConstantEqNodes.get(i);
				EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> inNode2 = inVarsAndConstantEqNodes.get(j);

				if (inNode1 == inNode2) {
					// no need to disequate two identical nodes
					continue;
				}
		
				if (state.areUnEqual(inNode1.nodeIdentifier.getEqNode(), inNode2.nodeIdentifier.getEqNode())) {
					builder.addDisEquality(inNode1.nodeIdentifier, inNode2.nodeIdentifier);
				}
			}
		}

		final VPTfState stateWithDisEqualitiesAdded = builder.build();

		Set<VPTfState> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);

		for (int i = 0; i < inVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> inNode1 = inVarsAndConstantEqNodes.get(i);
				EqGraphNode<VPNodeIdentifier, VPArrayIdentifier> inNode2 = inVarsAndConstantEqNodes.get(j);

				if (inNode1 == inNode2) {
					// no need to equate two identical nodes
					continue;
				}
			
				if (state.areEqual(inNode1.nodeIdentifier.getEqNode(), inNode2.nodeIdentifier.getEqNode())) {
					resultStates = VPFactoryHelpers.addEquality(inNode1.nodeIdentifier, inNode2.nodeIdentifier, resultStates, this);
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
