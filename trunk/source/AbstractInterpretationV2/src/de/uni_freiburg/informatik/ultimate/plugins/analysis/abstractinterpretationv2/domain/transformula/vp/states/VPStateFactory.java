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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainHelpers;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainPreanalysis;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPTransFormulaStateBuilderPreparer;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqAtomicBaseNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunctionNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNonAtomicBaseNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfArrayIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.VPTfNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 */
public class VPStateFactory<ACTION extends IIcfgTransition<IcfgLocation>>
		implements IVPFactory<VPState<ACTION>, EqNode, IProgramVarOrConst> {
	
	private final VPDomain<ACTION> mDomain;
	private final Map<Set<IProgramVarOrConst>, VPStateBottom<ACTION>> mBottomStates = new HashMap<>();
	private final VPTransFormulaStateBuilderPreparer mTfPreparer;
	private final VPDomainPreanalysis mPreAnalysis;

	public VPStateFactory(final VPDomain<ACTION> domain, final VPTransFormulaStateBuilderPreparer tfPreparer) {
		mDomain = domain;
		mTfPreparer = tfPreparer;
		mPreAnalysis = domain.getPreAnalysis();
	}

	@Override
	public IVPStateOrTfStateBuilder<VPState<ACTION>, EqNode, IProgramVarOrConst>
			createEmptyStateBuilder(final TransFormula tf) {
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
		final Set<IProgramVarOrConst> vars = new HashSet<>();
		builder.addVars(vars);

		builder.setIsTop(true);

		return builder;
	}

	@Override
	public VPStateBottom<ACTION> getBottomState(final Set<IProgramVarOrConst> newVars) {
		VPStateBottom<ACTION> result = mBottomStates.get(newVars);
		if (result == null) {
			result = new VPStateBottom<>(mDomain, newVars);
			mBottomStates.put(newVars, result);
		}
		return result;
	}

	public VPState<ACTION> getTopState(final Set<IProgramVarOrConst> vars) {
		return createEmptyStateBuilder().addVars(vars).build();
	}

	@Override
	public VPStateBuilder<ACTION> copy(final VPState<ACTION> originalState) {
		// if (originalState.isBottom()) {
		// return new VPStateBottomBuilder<>(mDomain).setVars(originalState.getVariables());
		// }
		assert !originalState.isBottom() : "no need to copy a bottom state, right?..";

		final VPStateBuilder<ACTION> builder = createEmptyStateBuilder();
		builder.setIsTop(originalState.isTop());
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(builder.mDisEqualitySet, builder);

		for (final EqNode eqNode : mPreAnalysis.getTermToEqNodeMap().values()) {
			final EqGraphNode<EqNode, IProgramVarOrConst> newGraphNode = builder.getEqGraphNode(eqNode);
			final EqGraphNode<EqNode, IProgramVarOrConst> oldGraphNode =
					originalState.getEqNodeToEqGraphNodeMap().get(eqNode);
			EqGraphNode.copyFields(oldGraphNode, newGraphNode, builder);
			// assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(builder.mDisEqualitySet, builder);
			assert !originalState.isTop() || newGraphNode.getRepresentative() == newGraphNode;
		}

		for (final VPDomainSymmetricPair<EqNode> pair : originalState.getDisEqualities()) {
			builder.addDisEquality(pair);
			assert !originalState.isTop() || pair.getFirst().isLiteral()
					&& pair.getSecond().isLiteral() : "The only disequalites in a top state are between constants";
		}

		builder.addVars(originalState.getVariables());

		assert builder.mVars.equals(originalState.getVariables());
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(builder.mDisEqualitySet, builder);
		assert VPDomainHelpers.disEqualityRelationIrreflexive(builder.mDisEqualitySet, builder);
		return builder;
	}

	/**
	 * Takes a set of TransitionStates (VPTfState) and a TransFormula. Converts the transition-states to normal states
	 * (VPState<ACTION>), essentially by projecting the transition state to the outVars of the given TransFormula.
	 *
	 * @param tfStates
	 * @param assignedVars
	 * @param oldState the state that the tfStates should be "patched over"
	 * @return
	 */
	public Set<VPState<ACTION>> convertToStates(final Set<VPTfState> tfStates, final Set<IProgramVar> assignedVars, 
			final VPState<ACTION> oldState) {
		final Set<VPState<ACTION>> result = new HashSet<>();

		for (final VPTfState tfState : tfStates) {
			result.add(convertToState(tfState, assignedVars, oldState));
		}

		return result;
	}

	/*
	 * (first) plan: for every two outVars, query which (dis-)equalities hold for them TODO: naive (quadratic)
	 * implementation in the future perhaps: work on the graph directly
	 */
	private VPState<ACTION> convertToState(final VPTfState tfState, final Set<IProgramVar> assignedVars, 
			final VPState<ACTION> oldState) {
		if (isDebugMode()) {
			getLogger().debug("VPStateFactory: convertToState(..) (begin)");
		}
		if (tfState.isBottom()) {
			return getBottomState(tfState.getVariables());
		}

		if (tfState.isTop()) {
			return oldState;
		}

		/*
		 * We are projecting the state to what it says about - outVars of the given TransFormula tf - constants
		 */
		final Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> outVarsAndConstantEqNodeSet = new HashSet<>();
		for (final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> node : tfState.getAllEqGraphNodes()) {
			if (node.nodeIdentifier.isOutOrThrough()) {
				outVarsAndConstantEqNodeSet.add(node);
			}
		}
		final List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> outVarsAndConstantEqNodes =
				new ArrayList<>(outVarsAndConstantEqNodeSet);
		
		Set<VPState<ACTION>> statesWithDisEqualitiesAdded = Collections.singleton(
				havocVariables(assignedVars, oldState));

		assert oldState.getVariables().containsAll(tfState.getVariables()) : "reactivate below code!";
//		final VPStateBuilder<ACTION> builder = copy(havocVariables(assignedVars, oldState));
//		builder.addVars(tfState.getVariables());
//		Set<VPState<ACTION>> statesWithDisEqualitiesAdded = Collections.singleton(builder.build());

//				new HashSet<>();
//		statesWithDisEqualitiesAdded.add(builder.build());

		for (int i = 0; i < outVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outNode1 = outVarsAndConstantEqNodes.get(i);
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outNode2 = outVarsAndConstantEqNodes.get(j);

				if (outNode1 == outNode2) {
					assert false;
					continue;
				}

				if (tfState.areUnEqual(outNode1.nodeIdentifier, outNode2.nodeIdentifier)) {
					statesWithDisEqualitiesAdded = VPFactoryHelpers.addDisEquality(outNode1.nodeIdentifier.getEqNode(),
							outNode2.nodeIdentifier.getEqNode(), statesWithDisEqualitiesAdded, this);
				}
			}
		}

		Set<VPState<ACTION>> resultStates = Collections.unmodifiableSet(statesWithDisEqualitiesAdded);
//				new HashSet<>();
//		resultStates.addAll(statesWithDisEqualitiesAdded);

		for (int i = 0; i < outVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outNode1 = outVarsAndConstantEqNodes.get(i);
				final EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outNode2 = outVarsAndConstantEqNodes.get(j);

				if (outNode1 == outNode2) {
					// no need to equate two identical nodes
					continue;
				}

				if (tfState.areEqual(outNode1.nodeIdentifier, outNode2.nodeIdentifier)) {
					resultStates = VPFactoryHelpers.addEquality(outNode1.nodeIdentifier.getEqNode(),
							outNode2.nodeIdentifier.getEqNode(), resultStates, this);
				}
			}
		}
		if (isDebugMode()) {
			getLogger().debug("VPStateFactory: convertToState(..) (end)");
		}
		assert resultStates.size() == 1 : "??";
		return resultStates.iterator().next();
	}

	@Override
	public Set<EqNode> getFunctionNodesForArray(final VPState<ACTION> state, final IProgramVarOrConst firstArray) {
		return getFunctionNodesForArray(firstArray);
	}

	public Set<EqNode> getFunctionNodesForArray(final IProgramVarOrConst firstArray) {
		final Set<EqFunctionNode> image = mPreAnalysis.getArrayIdToFnNodeMap().getImage(firstArray);
		return image.stream().map(node -> (EqNode) node).collect(Collectors.toSet());
	}

	public VPState<ACTION> disjoinAll(final Set<VPState<ACTION>> statesForCurrentEc) {
		return VPFactoryHelpers.disjoinAll(statesForCurrentEc, this);
	}

	@Override
	public ILogger getLogger() {
		return mDomain.getLogger();
	}
	
	@Override
	public boolean isDebugMode() {
		return mDomain.isDebugMode();
	}

	@Override
	public Benchmark getBenchmark() {
		return mPreAnalysis.getBenchmark();
	}

	/**
	 * To havoc a node. There are three main parts to handle: (1) Handling the outgoing edge chain. (2) Handling the
	 * incoming edges. (3) Handling the node itself.
	 *
	 * @param EqGraphNode
	 *            to be havoc
	 */
	public VPState<ACTION> havoc(final EqNode nodeToBeHavocced, final VPState<ACTION> originalState) {
		if (originalState.isBottom()) {
			return originalState;
		}
		
		// assert !node.isLiteral() : "cannot havoc a literal";
		assert nodeToBeHavocced.getTerm().getFreeVars().length > 0 : "cannot havoc a constant term";
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(originalState.getDisEqualities(),
				originalState);

		final VPStateBuilder<ACTION> builder1 = copy(originalState);
		EqGraphNode<EqNode, IProgramVarOrConst> graphNodeForNodeToBeHavocced =
				builder1.getEqGraphNode(nodeToBeHavocced);
		
		// TODO: determine if state becomes top through the havoc!

		/*
		 * Handling the outgoing edge chain
		 */
		final EqGraphNode<EqNode, IProgramVarOrConst> firstRepresentative =
				graphNodeForNodeToBeHavocced.getRepresentative();
		EqGraphNode<EqNode, IProgramVarOrConst> nextRepresentative = firstRepresentative;
		nextRepresentative.getReverseRepresentative().remove(graphNodeForNodeToBeHavocced);
		while (!(nextRepresentative.equals(nextRepresentative.getRepresentative()))) {
			nextRepresentative.getCcpar().removeAll(graphNodeForNodeToBeHavocced.getCcpar());
			for (final Entry<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> entry : graphNodeForNodeToBeHavocced
					.getCcchild().entrySet()) {
				nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
			}
			nextRepresentative = nextRepresentative.getRepresentative();
		}
		nextRepresentative.getCcpar().removeAll(graphNodeForNodeToBeHavocced.getCcpar());
		final HashRelation<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> copyOfGraphNodeCcchild =
				new HashRelation<>();
		for (final Entry<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> entry : graphNodeForNodeToBeHavocced
				.getCcchild().entrySet()) {
			copyOfGraphNodeCcchild.addPair(entry.getKey(), entry.getValue());
		}
		for (final Entry<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> entry : copyOfGraphNodeCcchild
				.entrySet()) {
			nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
		}

		/*
		 * Handling the incoming edges (reverseRepresentative). Point nodes in reverseRepresentative to the
		 * representative of the node that is being havoc. For example, y -> x -> z. Havoc x, then we have y -> z But if
		 * the node that is being havoc is its own representative, then point nodes in reverseRepresentative to one of
		 * them. For example, y -> x <- z, Havoc x, then we have y -> z or z -> y.
		 */
		EqGraphNode<EqNode, IProgramVarOrConst> firstReserveRepresentativeNode = null;
		if (!graphNodeForNodeToBeHavocced.getReverseRepresentative().isEmpty()) {
			firstReserveRepresentativeNode = graphNodeForNodeToBeHavocced.getReverseRepresentative().iterator().next();
		}
		for (final EqGraphNode<EqNode, IProgramVarOrConst> reverseNode : graphNodeForNodeToBeHavocced
				.getReverseRepresentative()) {
			// first reset the representative of all the reverseRepresentative nodes.
			reverseNode.setRepresentative(reverseNode);
		}
		
		boolean havocNodeIsItsRepresentative = false;
		VPState<ACTION> resultState = builder1.build();
		for (final EqGraphNode<EqNode, IProgramVarOrConst> reverseNode : graphNodeForNodeToBeHavocced
				.getReverseRepresentative()) {
			// case y -> x <- z
			if (firstRepresentative.equals(graphNodeForNodeToBeHavocced)) {
				havocNodeIsItsRepresentative = true;
				if (graphNodeForNodeToBeHavocced.getReverseRepresentative().size() > 1) {
					assert firstReserveRepresentativeNode != null;
					resultState = disjoinAll(VPFactoryHelpers.addEquality(reverseNode.nodeIdentifier,
							firstReserveRepresentativeNode.nodeIdentifier, resultState, this));
				}
			} else { // case y -> x -> z
				resultState = disjoinAll(VPFactoryHelpers.addEquality(reverseNode.nodeIdentifier,
						firstRepresentative.nodeIdentifier, resultState, this));
			}
		}
		
		final VPStateBuilder<ACTION> builder2 = copy(resultState);
		graphNodeForNodeToBeHavocced = builder2.getEqGraphNode(nodeToBeHavocced);
		
		/*
		 * Handling the nodeToBeHavocced itself: First update disequality set. Then set nodeToBeHavocced to initial.
		 */
		if (havocNodeIsItsRepresentative) {
			final Set<VPDomainSymmetricPair<EqNode>> newDisEqualitySet = new HashSet<>();
			for (final VPDomainSymmetricPair<EqNode> pair : builder2.getDisEqualitySet()) {
				if (pair.contains(graphNodeForNodeToBeHavocced.nodeIdentifier)) {
					newDisEqualitySet.add(new VPDomainSymmetricPair<EqNode>(
							pair.getOther(graphNodeForNodeToBeHavocced.nodeIdentifier),
							resultState.find(firstReserveRepresentativeNode.nodeIdentifier)));
				} else {
					newDisEqualitySet.add(pair);
				}
			}
			builder2.clearDisEqualitySet();
			builder2.addDisEqualites(newDisEqualitySet);
		} else {
			// do nothing: no need to update disequality set, because if x is not representative, then x should not be
			// in disequality set.
		}
		graphNodeForNodeToBeHavocced.setNodeToInitial();

		if (nodeToBeHavocced instanceof EqFunctionNode) {
			builder2.restorePropagation((EqFunctionNode) nodeToBeHavocced);
		}
		
		resultState = builder2.build();
		
		// also havoc the function nodes which index had been havoc.
		if (!graphNodeForNodeToBeHavocced.getInitCcpar().isEmpty()) {
			for (final EqGraphNode<EqNode, IProgramVarOrConst> initCcpar : graphNodeForNodeToBeHavocced
					.getInitCcpar()) {
				resultState = havoc(initCcpar.nodeIdentifier, resultState);
			}
		}
		
		/*
		 * havoc all the non-atomic EqNodes which depend on this one
		 */
		if (nodeToBeHavocced instanceof EqAtomicBaseNode) {
			for (final EqNonAtomicBaseNode dependentNode : ((EqAtomicBaseNode) nodeToBeHavocced)
					.getDependentNonAtomicBaseNodes()) {
				resultState = havoc(dependentNode, resultState);
			}
		}
		
		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(resultState.getDisEqualities(), resultState);
		// assert VPDomainHelpers.isHavocced(nodeToBeHavocced, resultState);
		return resultState;
	}
	
	/**
	 * To havoc an array. All the element in this array will be havoc.
	 *
	 * @param term
	 */
	public VPState<ACTION> havocArray(final IProgramVarOrConst array, final VPState<ACTION> originalState) {
		VPState<ACTION> resultState = copy(originalState).build();
		
		for (final EqNode eqNode : originalState.getEqNodeToEqGraphNodeMap().keySet()) {
			if (eqNode.getAllFunctions().contains(array)) {
				resultState = this.havoc(eqNode, resultState);
			}
		}

		// assert VPDomainHelpers.isHavocced(array, resultState);
		return resultState;
	}

	/**
	 * To havoc a set of nodes. If this set contains array, it will not be havoc here.
	 *
	 * @param assignmentVars
	 */
	public VPState<ACTION> havocVariables(final Set<IProgramVar> assignmentVars, final VPState<ACTION> originalState) {
		VPState<ACTION> resultState = copy(originalState).build();
		for (final IProgramVar var : assignmentVars) {
			
			if (var.getTerm().getSort().isArraySort()) {
				resultState = havocArray(var, resultState);
				continue;
			}

			final EqNode node = mDomain.getPreAnalysis().getEqNode(var.getTerm(), Collections.emptyMap());
			
			if (node != null) {
				resultState = havoc(node, resultState);
			}
		}
		return resultState;
	}
	
}
