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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPTfStateBuilderPreparer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class VpTfStateFactory implements IVPFactory<VPTfState, VPTfNodeIdentifier, VPTfArrayIdentifier> {
	
	private final VPTfStateBuilderPreparer mTfStatePreparer;
	private final VPDomainPreanalysis mPreAnalysis;

	private final NestedMap2<Set<IProgramVarOrConst>, Set<IProgramVarOrConst>, VPTfBottomState> mVarsToBottomState = 
			new NestedMap2<>();

	public VpTfStateFactory(final VPTfStateBuilderPreparer tfStatePreparer,
			final VPDomainPreanalysis preAnalysis) {
		mTfStatePreparer = tfStatePreparer;
		mPreAnalysis = preAnalysis;
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

	public Set<VPTfState> handleArrayEquality(final Term lhs, final Term rhs, final VPTfState tfPreState) {
		return VPFactoryHelpers.arrayEquality(tfPreState.getArrayIdentifier(lhs), tfPreState.getArrayIdentifier(rhs),
				tfPreState, this);
	}

	@Override
	public VPTfStateBuilder copy(final VPTfState state) {
		assert !state.isBottom();

		final VPTfStateBuilder builder = createFreshVanillaStateBuilder(state.getAction());
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(builder.mDisEqualitySet, builder);
		builder.setIsTop(state.isTop());

		for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> egnInOldState : state.getAllEqGraphNodes()) {
			final VPTfNodeIdentifier nodeId = egnInOldState.mNodeIdentifier;
			final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> newGraphNode = builder.getEqGraphNode(nodeId);
			assert newGraphNode != null;
			EqGraphNode.copyFields(egnInOldState, newGraphNode, builder);
			assert !state.isTop() || newGraphNode.getRepresentative() == newGraphNode;
		}

		for (final VPDomainSymmetricPair<VPTfNodeIdentifier> pair : state.getDisEqualities()) {
			builder.addDisEquality(pair.getFirst(), pair.getSecond());
			// assert !state.isTop() || pair.mFst.isLiteral()
			// && pair.mSnd.isLiteral() : "The only disequalites in a top state are between constants";
		}

//		builder.addInVars(new HashSet<>(state.getInVariables()));
//		builder.addOutVars(new HashSet<>(state.getOutVariables()));

		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(builder.mDisEqualitySet, builder);
		assert VPDomainHelpers.disEqualityRelationIrreflexive(builder.mDisEqualitySet, builder);
		builder.setIsTop(state.isTop());
		// assert builder.mVars.equals(state.getVariables());
		return builder;
	}

	@Override
	public VPTfState getBottomState(final VPTfState originalState) {
		return getBottomState(originalState.getInVariables(), originalState.getOutVariables());
	}

	VPTfState getBottomState(final Set<IProgramVarOrConst> inVars, final Set<IProgramVarOrConst> outVars) {
		VPTfBottomState result = mVarsToBottomState.get(inVars, outVars);
		if (result == null) {
			result = new VPTfBottomState(inVars, outVars);
			mVarsToBottomState.put(inVars, outVars, result);
		}
		return result;
	}

	/**
	 * Obtain the vanilla builder for the given TransFormula, make a (deep) copy of it and return it.
	 */
	@Override
//	public VPTfStateBuilder createFreshVanillaStateBuilder(final TransFormula tf) {
	public VPTfStateBuilder createFreshVanillaStateBuilder(final IAction action) {
		final VPTfStateBuilder vanillaBuilder = mTfStatePreparer.getVPTfStateBuilder(action);
		assert vanillaBuilder.isTopConsistent();

		final VPTfStateBuilder result = new VPTfStateBuilder(vanillaBuilder);
		assert result.isTopConsistent();
		return result;
	}

	/**
	 * Given a VPState and a TransFormula, this 
	 *  <li> acquires the "vanilla" VPTfStateBuilder for the TransFormula 
	 *  <li> "patches in" the given state, i.e., collects everything that the state knows about the inVars of the 
	 * 	     TransFormula and updates the VPTfStateBuidler accordingly
	 *
	 * @param state
	 * @param tf
	 * @return
	 */
//	public VPTfState createTfState(final VPState<?> state, final UnmodifiableTransFormula tf) {
	public Set<VPTfState> createTfState(final VPState<?> state, final IAction action) {
		if (isDebugMode()) {
			getLogger().debug("VPTfStateFactory: createTfState(..) (begin)");
		}

		if (state.isBottom()) {
			// FIXME extra builder for var signature: a bit hacky..
			return Collections.singleton(getBottomState(mTfStatePreparer.getVPTfStateBuilder(action).build())); 
		}

		if (state.isTop()) {
			final VPTfStateBuilder builder = createFreshVanillaStateBuilder(action);
//			builder.addVars(state.getVariables());
			return Collections.singleton(builder.build());
		}

		final VPTfStateBuilder builder = createFreshVanillaStateBuilder(action);
//		builder.addVars(state.getVariables());
		
		final Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> inVarsAndConstantEqNodeSet = new HashSet<>();
		for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> node : builder.getAllEqGraphNodes()) {
			if (node.mNodeIdentifier.isInOrThrough()) {
				inVarsAndConstantEqNodeSet.add(node);
			}
		}
		
		final List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> inVarsAndConstantEqNodes =
				new ArrayList<>(inVarsAndConstantEqNodeSet);

		for (int i = 0; i < inVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> inNode1 = inVarsAndConstantEqNodes.get(i);
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> inNode2 = inVarsAndConstantEqNodes.get(j);
				
				assert !inNode1.equals(inNode2);

//				if (inNode1 == inNode2) {
//					// no need to disequate two identical nodes
//					continue;
//				}

				if (state.areUnEqual(inNode1.mNodeIdentifier.getEqNode(), inNode2.mNodeIdentifier.getEqNode())) {
					builder.addDisEquality(inNode1.mNodeIdentifier, inNode2.mNodeIdentifier);
				}
			}
		}

		final VPTfState stateWithDisEqualitiesAdded = builder.build();

		Set<VPTfState> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);

		for (int i = 0; i < inVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> inNode1 = inVarsAndConstantEqNodes.get(i);
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> inNode2 = inVarsAndConstantEqNodes.get(j);

				if (inNode1 == inNode2) {
					// no need to equate two identical nodes
					continue;
				}

				if (state.areEqual(inNode1.mNodeIdentifier.getEqNode(), inNode2.mNodeIdentifier.getEqNode())) {
//					assert resultStates.size() == 1 : "??";
					resultStates = VPFactoryHelpers.addEquality(inNode1.mNodeIdentifier, inNode2.mNodeIdentifier,
							resultStates, this);
//					assert resultStates.size() == 1 : "??";
//					if (resultStates.size() > 1) {
//						//FIXME: ... or should we allow multiple initial tf states??
//						resultStates = Collections.singleton(VPFactoryHelpers.disjoinAll(resultStates, this));
//					}
				}
			}
		}

		if (isDebugMode()) {
			getLogger().debug("VPTfStateFactory: createTfState(..) (end)");
		}
		assert resultStates.size() >0 : "??";
		return resultStates;
	}

	@Override
	public Set<VPTfNodeIdentifier> getFunctionNodesForArray(final VPTfState tfState,
			final VPTfArrayIdentifier firstArray) {
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
