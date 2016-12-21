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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;

public class VPStateFactory<ACTION extends IIcfgTransition<IcfgLocation>> implements IVPFactory<VPState<ACTION>, EqNode, IProgramVarOrConst> {

	private final VPDomain<ACTION> mDomain;
	private final Map<Set<IProgramVar>, VPStateBottom<ACTION>> mBottomStates = new HashMap<>();

	public VPStateFactory(final VPDomain<ACTION> domain) {
		mDomain = domain;
	}

	@Override
	public IVPStateOrTfStateBuilder<VPState<ACTION>, EqNode, IProgramVarOrConst> createEmptyStateBuilder(final TransFormula tf) {
		return createEmptyStateBuilder();
	}

	public VPStateBuilder<ACTION> createEmptyStateBuilder() {

		final VPStateBuilder<ACTION> builder = new VPStateBuilder<>(mDomain);

		/*
		 * When all EqGraphNodes for the VPState<ACTION> have been created, we can set their initCcpar and initCcchild
		 * fields
		 */
		for (final EqGraphNode<EqNode, IProgramVarOrConst> egn : builder.getAllEqGraphNodes()) {
			egn.setupNode();
		}

		/*
		 * Generate disequality set for constants
		 */
//		final Set<VPNodeIdentifier> literalSet = mDomain.getLiteralEqNodes().stream()
//				.map(eqNode -> new VPNodeIdentifier(eqNode)).collect(Collectors.toSet());
		final Set<EqNode> literalSet = mDomain.getLiteralEqNodes();
		final Set<VPDomainSymmetricPair<EqNode>> disEqualitySet = new HashSet<>();
		for (final EqNode node1 : literalSet) {
			for (final EqNode node2 : literalSet) {
				if (!node1.equals(node2)) {
					disEqualitySet.add(new VPDomainSymmetricPair<>(node1, node2));
				}
			}
		}
		builder.addDisEqualites(disEqualitySet);

		/*
		 * The set of tracked variables (as exposed to the fixpointengine) is empty, initially.
		 */
		final Set<IProgramVar> vars = new HashSet<>();
		builder.addVars(vars);

		builder.setIsTop(true);

		return builder;
	}

	@Override
	public VPStateBottom<ACTION> getBottomState(final Set<IProgramVar> set) {
		VPStateBottom<ACTION> result = mBottomStates.get(set);
		if (result == null) {
//			final VPStateBottomBuilder<ACTION> builder = new VPStateBottomBuilder<>(mDomain);
			result = new VPStateBottom<>(mDomain, set);
			mBottomStates.put(set, result);
		}
		return result;
	}

	public VPState<ACTION> getTopState(final Set<IProgramVar> vars) {
		return createEmptyStateBuilder().addVars(vars).build();
	}

	@Override
	public VPStateBuilder<ACTION> copy(final VPState<ACTION> originalState) {
//		if (originalState.isBottom()) {
//			return new VPStateBottomBuilder<>(mDomain).setVars(originalState.getVariables());
//		}
		assert !originalState.isBottom() : "no need to copy a bottom state, right?..";

		final VPStateBuilder<ACTION> builder = createEmptyStateBuilder();
		builder.setIsTop(originalState.isTop());

		for (final EqNode eqNode : mDomain.getTermToEqNodeMap().values()) {
			final EqGraphNode<EqNode, IProgramVarOrConst> newGraphNode = builder.getEqGraphNode(eqNode);
			final EqGraphNode<EqNode, IProgramVarOrConst> oldGraphNode = originalState.getEqNodeToEqGraphNodeMap().get(eqNode);
			EqGraphNode.copyFields(oldGraphNode, newGraphNode, builder);
			assert !originalState.isTop() || newGraphNode.getRepresentative() == newGraphNode;
		}

		for (final VPDomainSymmetricPair<EqNode> pair : originalState.getDisEqualities()) {
			builder.addDisEquality(pair);
			assert !originalState.isTop() || pair.mFst.isLiteral()
					&& pair.mSnd.isLiteral() : "The only disequalites in a top state are between constants";
		}

		builder.addVars(originalState.getVariables());


		assert builder.mVars.equals(originalState.getVariables());
		return builder;
	}

	/**
	 * Takes a set of TransitionStates (VPTfState) and a TransFormula. Converts the transition-states to normal states
	 * (VPState<ACTION>), essentially by projecting the transition state to the outVars of the given TransFormula.
	 * 
	 * @param resultTfStates
	 * @param tf
	 * @return
	 */
	public Set<VPState<ACTION>> convertToStates(final Set<VPTfState> tfStates, final UnmodifiableTransFormula tf) {
		final Set<VPState<ACTION>> result = new HashSet<>();

		for (final VPTfState tfState : tfStates) {
			result.add(convertToState(tfState, tf));
		}

		return result;
	}

	/*
	 * (first) plan: for every two outVars, query which (dis-)equalities hold for them TODO: naive (quadratic)
	 * implementation in the future perhaps: work on the graph directly
	 */
	private VPState<ACTION> convertToState(final VPTfState tfState, final UnmodifiableTransFormula tf) {
		if (tfState.isBottom()) {
			return getBottomState(tfState.getVariables());
		}

		if (tfState.isTop()) {
			final VPStateBuilder<ACTION> builder = createEmptyStateBuilder();
			builder.addVars(tfState.getVariables());
			return builder.build();
		}

		final VPStateBuilder<ACTION> builder = createEmptyStateBuilder();
		builder.addVars(tfState.getVariables());
		builder.setIsTop(true);

		for (final Entry<IProgramVar, TermVariable> outVar1 : tf.getOutVars().entrySet()) {
			if (outVar1.getKey().getTerm().getSort().isArraySort()) {
				continue;
			}
			for (final Entry<IProgramVar, TermVariable> outVar2 : tf.getOutVars().entrySet()) {
				if (outVar2.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}

				final EqNode eqNodeForOutVar1 =
						mDomain.getPreAnalysis().getEqNode(outVar1.getKey());
				final EqNode eqNodeForOutVar2 =
						mDomain.getPreAnalysis().getEqNode(outVar2.getKey());
				assert eqNodeForOutVar1 != null;
				assert eqNodeForOutVar2 != null;
				final VPNodeIdentifier id1 = new VPNodeIdentifier(eqNodeForOutVar1, 
						VPDomainHelpers.projectToTerm(tf.getInVars(), outVar1.getValue()),
						VPDomainHelpers.projectToTerm(tf.getOutVars(), outVar1.getValue()));
				final VPNodeIdentifier id2 = new VPNodeIdentifier(eqNodeForOutVar2, 
						VPDomainHelpers.projectToTerm(tf.getInVars(), outVar2.getValue()),
						VPDomainHelpers.projectToTerm(tf.getOutVars(), outVar2.getValue()));

				if (tfState.areUnEqual(id1, id2)) {
					builder.addDisEquality(eqNodeForOutVar1, eqNodeForOutVar2);
					builder.setIsTop(false);
				}
			}
		}

		final VPState<ACTION> stateWithDisEqualitiesAdded = builder.build();

		Set<VPState<ACTION>> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);

		for (final Entry<IProgramVar, TermVariable> outVar1 : tf.getOutVars().entrySet()) {
			if (outVar1.getKey().getTerm().getSort().isArraySort()) {
				continue;
			}
			for (final Entry<IProgramVar, TermVariable> outVar2 : tf.getOutVars().entrySet()) {
				if (outVar2.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				final EqNode eqNodeForOutVar1 =
						mDomain.getPreAnalysis().getEqNode(outVar1.getKey().getTerm(), Collections.emptyMap());
				final EqNode eqNodeForOutVar2 =
						mDomain.getPreAnalysis().getEqNode(outVar2.getKey().getTerm(), Collections.emptyMap());
				assert eqNodeForOutVar1 != null;
				assert eqNodeForOutVar2 != null;
				final VPNodeIdentifier id1 = new VPNodeIdentifier(eqNodeForOutVar1, 
						VPDomainHelpers.projectToTerm(tf.getInVars(), outVar1.getValue()),
						VPDomainHelpers.projectToTerm(tf.getOutVars(), outVar1.getValue()));
				final VPNodeIdentifier id2 = new VPNodeIdentifier(eqNodeForOutVar2, 
						VPDomainHelpers.projectToTerm(tf.getInVars(), outVar2.getValue()),
						VPDomainHelpers.projectToTerm(tf.getOutVars(), outVar2.getValue()));

				if (tfState.areEqual(id1, id2)) {
					resultStates = VPFactoryHelpers.addEquality(eqNodeForOutVar1, eqNodeForOutVar2, resultStates, this);
					builder.setIsTop(false);
				}
			}
		}

		assert resultStates.size() == 1 : "??";
		return resultStates.iterator().next();
	}

	@Override
	public Set<EqNode> getFunctionNodesForArray(final VPState<ACTION> state,
			final IProgramVarOrConst firstArray) {
		return getFunctionNodesForArray(firstArray);
	}

	public Set<EqNode> getFunctionNodesForArray(final IProgramVarOrConst firstArray) {
		final Set<EqFunctionNode> image = mDomain.getArrayIdToEqFnNodeMap().getImage(firstArray);
		return image.stream().map(node -> (EqNode) node).collect(Collectors.toSet());
	}

	public VPState<ACTION> disjoinAll(final Set<VPState<ACTION>> statesForCurrentEc) {
		return VPFactoryHelpers.disjoinAll(statesForCurrentEc, this);
	}

}
