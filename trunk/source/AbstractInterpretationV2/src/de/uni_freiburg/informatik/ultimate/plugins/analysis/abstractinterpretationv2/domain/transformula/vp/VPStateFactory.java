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
import java.util.stream.Collectors;

import javax.xml.soap.Node;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;

public class VPStateFactory<ACTION extends IIcfgTransition<IcfgLocation>> implements IVPFactory<VPState<ACTION>, EqNode, IProgramVarOrConst> {

	private final VPDomain<ACTION> mDomain;
	private final Map<Set<IProgramVar>, VPStateBottom<ACTION>> mBottomStates = new HashMap<>();
	private final VPTransFormulaStateBuilderPreparer mTfPreparer;
	private VPDomainPreanalysis mPreAnalysis;

	public VPStateFactory(final VPDomain<ACTION> domain, final VPTransFormulaStateBuilderPreparer tfPreparer) {
		mDomain = domain;
		mTfPreparer = tfPreparer;
		mPreAnalysis = domain.getPreAnalysis();
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
	 * @param oldState the state that the tfStates should be "patched over"
	 * @return
	 */
	public Set<VPState<ACTION>> convertToStates(final Set<VPTfState> tfStates, final UnmodifiableTransFormula tf, VPState<ACTION> oldState) {
		final Set<VPState<ACTION>> result = new HashSet<>();

		for (final VPTfState tfState : tfStates) {
			result.add(convertToState(tfState, tf, oldState));
		}

		return result;
	}

	/*
	 * (first) plan: for every two outVars, query which (dis-)equalities hold for them TODO: naive (quadratic)
	 * implementation in the future perhaps: work on the graph directly
	 */
	private VPState<ACTION> convertToState(final VPTfState tfState, final UnmodifiableTransFormula tf, VPState<ACTION> oldState) {
		if (isDebugMode()) {
			getLogger().debug("VPStateFactory: convertToState(..) (begin)");
		}
		if (tfState.isBottom()) {
			return getBottomState(tfState.getVariables());
		}

		if (tfState.isTop()) {
//			final VPStateBuilder<ACTION> builder = createEmptyStateBuilder();
//			builder.addVars(tfState.getVariables());
//			return builder.build();
			return oldState;
		}
		
		/*
		 * strategy:
		 * we first add disequalites from the transition state
		 *  --> without the presence of equalities they induce no propagations, so we can work on one builder
		 * then we add equalities from the transition state
		 */
		
		/*
		 * We are projecting the state to what it says about 
		 *  - outVars of the given TransFormula tf
		 *  - constants
		 */
		Set<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> outVarsAndConstantEqNodeSet = new HashSet<>();
		for (EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> node : tfState.getAllEqGraphNodes()) {
			if (node.nodeIdentifier.getEqNode() == null) {
				// auxvar node
				continue;
			}
			if (node.nodeIdentifier.getEqNode().isConstant()) {
				// we need to track all constants
				outVarsAndConstantEqNodeSet.add(node);
				continue;
			}
			
			HashSet<IProgramVar> nodeVars = new HashSet<>(node.nodeIdentifier.getEqNode().getVariables());
			nodeVars.retainAll(tf.getOutVars().keySet());
			if (!nodeVars.isEmpty()) {
				// we need to track all nodes that talk about at least one outvar
				outVarsAndConstantEqNodeSet.add(node);
			}
		}
//		for (IProgramVar pv : tf.getOutVars().keySet()) {
//			EqNode pvEqnode = mPreAnalysis.getEqNode(pv);
//			if (pvEqnode != null) {
//				outVarsAndConstantEqNodes.add(pvEqnode);
//			}
//		}
//		outVarsAndConstantEqNodes.addAll(mTfPreparer.getAllConstantEqNodes());
		List<EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier>> outVarsAndConstantEqNodes = new ArrayList<>(outVarsAndConstantEqNodeSet);

		final VPStateBuilder<ACTION> builder = copy(havocVariables(tf.getAssignedVars(), oldState));// TODO
		builder.addVars(tfState.getVariables());

		for (int i = 0; i < outVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outNode1 = outVarsAndConstantEqNodes.get(i);
				EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outNode2 = outVarsAndConstantEqNodes.get(j);

				if (outNode1 == outNode2) {
					// no need to disequate two identical nodes
					continue;
				}

//				VPNodeIdentifier id1 = new VPNodeIdentifier(outNode1, 
//						VPDomainHelpers.projectToVars(tf.getInVars(), outNode1.getVariables()),
//						VPDomainHelpers.projectToVars(tf.getOutVars(), outNode1.getVariables()));
//				VPNodeIdentifier id2 = new VPNodeIdentifier(outNode2, 
//						VPDomainHelpers.projectToVars(tf.getInVars(), outNode2.getVariables()),
//						VPDomainHelpers.projectToVars(tf.getOutVars(), outNode2.getVariables()));

				if (tfState.areUnEqual(outNode1.nodeIdentifier, outNode2.nodeIdentifier)) {
					builder.addDisEquality(outNode1.nodeIdentifier.getEqNode(), outNode2.nodeIdentifier.getEqNode());
				}
			}
		}

		final VPState<ACTION> stateWithDisEqualitiesAdded = builder.build();

		Set<VPState<ACTION>> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);

		for (int i = 0; i < outVarsAndConstantEqNodes.size(); i++) {
			for (int j = 0; j < i; j++) {
				EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outNode1 = outVarsAndConstantEqNodes.get(i);
				EqGraphNode<VPTfNodeIdentifier, VPTfArrayIdentifier> outNode2 = outVarsAndConstantEqNodes.get(j);

				if (outNode1 == outNode2) {
					// no need to equate two identical nodes
					continue;
				}
//				VPNodeIdentifier id1 = new VPNodeIdentifier(outNode1, 
//							VPDomainHelpers.projectToVars(tf.getInVars(), outNode1.getVariables()),
//							VPDomainHelpers.projectToVars(tf.getOutVars(), outNode1.getVariables()));
//				VPNodeIdentifier id2 = new VPNodeIdentifier(outNode2, 
//							VPDomainHelpers.projectToVars(tf.getInVars(), outNode2.getVariables()),
//							VPDomainHelpers.projectToVars(tf.getOutVars(), outNode2.getVariables()));

				if (tfState.areEqual(outNode1.nodeIdentifier, outNode2.nodeIdentifier)) {
					resultStates = VPFactoryHelpers.addEquality(
							outNode1.nodeIdentifier.getEqNode(), 
							outNode2.nodeIdentifier.getEqNode(), 
							resultStates, 
							this);
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
	 * To havoc a node. There are three main parts to handle: (1) Handling the
	 * outgoing edge chain. (2) Handling the incoming edges. (3) Handling the
	 * node itself.
	 * 
	 * @param EqGraphNode
	 *            to be havoc
	 */
	public VPState<ACTION> havoc(final EqNode node, final VPState<ACTION> originalState) {
		if (originalState.isBottom()) {
			return originalState;
		}
		
		//assert !node.isLiteral() : "cannot havoc a literal";
		assert node.getTerm().getFreeVars().length > 0 : "cannot havoc a constant term";
		
		
		VPStateBuilder<ACTION> builder = copy(originalState);
		EqGraphNode<EqNode, IProgramVarOrConst> graphNode = builder.getEqGraphNode(node);
		
		// TODO: determine if state becomes top through the havoc!

		// Handling the outgoing edge chain
		final EqGraphNode<EqNode, IProgramVarOrConst> firstRepresentative = graphNode.getRepresentative();
		EqGraphNode<EqNode, IProgramVarOrConst> nextRepresentative = firstRepresentative;
		nextRepresentative.getReverseRepresentative().remove(graphNode);
		while (!(nextRepresentative.equals(nextRepresentative.getRepresentative()))) {
			nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
			for (final Entry<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> entry : graphNode.getCcchild().entrySet()) {
				nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
			}
			nextRepresentative = nextRepresentative.getRepresentative();
		}
		nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
		HashRelation<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> copyOfGraphNodeCcchild = new HashRelation<>();
		for (final Entry<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> entry : graphNode.getCcchild().entrySet()) {
			copyOfGraphNodeCcchild.addPair(entry.getKey(), entry.getValue());
		}
		for (final Entry<IProgramVarOrConst, List<EqGraphNode<EqNode, IProgramVarOrConst>>> entry : copyOfGraphNodeCcchild.entrySet()) {
			nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
		}

		/*
		 *  Handling the incoming edges (reverseRepresentative).
		 *  Point nodes in reverseRepresentative to the representative of the node that is being havoc.
		 *  For example, y -> x -> z. Havoc x, then we have y -> z
		 *  But if the node that is being havoc is its own representative, 
		 *  then point nodes in reverseRepresentative to one of them.
		 *  For example, y -> x <- z, Havoc x, then we have y -> z or z -> y.
		 */
		EqGraphNode<EqNode, IProgramVarOrConst> firstReserveRepresentativeNode = null;
		if (!graphNode.getReverseRepresentative().isEmpty()) {
			firstReserveRepresentativeNode = graphNode.getReverseRepresentative().iterator().next();
		}
		for (final EqGraphNode<EqNode, IProgramVarOrConst> reverseNode : graphNode.getReverseRepresentative()) {
			// first reset the representative of all the reverseRepresentative nodes.
			reverseNode.setRepresentative(reverseNode);
		}
		
		boolean havocNodeIsItsRepresentative = false;
		VPState<ACTION> resultState = builder.build();
		for (final EqGraphNode<EqNode, IProgramVarOrConst> reverseNode : graphNode.getReverseRepresentative()) {
			// case y -> x <- z
			if (firstRepresentative.equals(graphNode)) {
				havocNodeIsItsRepresentative = true;
				if (graphNode.getReverseRepresentative().size() > 1) {
					assert firstReserveRepresentativeNode != null;
					resultState = disjoinAll(
								VPFactoryHelpers.addEquality(reverseNode.nodeIdentifier, firstReserveRepresentativeNode.nodeIdentifier, resultState, this));
				}
			} else { // case y -> x -> z
				resultState = disjoinAll(
						VPFactoryHelpers.addEquality(reverseNode.nodeIdentifier, firstRepresentative.nodeIdentifier, resultState, this));
			}
		}
		
		builder = copy(resultState);
		graphNode = builder.getEqGraphNode(node);
		
		/*
		 * Handling the node itself:
		 * First update disequality set.
		 * Then set havoc node to initial.
		 */
		if (havocNodeIsItsRepresentative) {
			Set<VPDomainSymmetricPair<EqNode>> newDisEqualitySet = new HashSet<>();
			for (VPDomainSymmetricPair<EqNode> pair : builder.getDisEqualitySet()) {
				if (pair.contains(graphNode.nodeIdentifier)) {
					newDisEqualitySet.add(
							new VPDomainSymmetricPair<EqNode>(
									pair.getOther(graphNode.nodeIdentifier), 
									resultState.find(firstReserveRepresentativeNode.nodeIdentifier)));
				} else {
					newDisEqualitySet.add(pair);
				}
			}
			builder.addDisEqualites(newDisEqualitySet);
		} else {
			// do nothing: no need to update disequality set, because if x is not representative, then x should not be in disequality set.
		}
//		if (graphNode.getRepresentative().equals(graphNode)) {
//			Set<VPDomainSymmetricPair<EqNode>> newSet = 
//					builder.getDisEqualitySet().stream()
//					.filter(pair -> !pair.contains(node))
//					.collect(Collectors.toSet());
//			builder.setDisEqualites(newSet);
//		}
		graphNode.setNodeToInitial();

		if (node instanceof EqFunctionNode) {
			builder.restorePropagation((EqFunctionNode) node);
		}
		resultState = builder.build();
		
		// also havoc the function nodes which index had been havoc.
		if (!graphNode.getInitCcpar().isEmpty()) {
			for (final EqGraphNode<EqNode, IProgramVarOrConst> initCcpar : graphNode.getInitCcpar()) {
				resultState = havoc(initCcpar.nodeIdentifier, resultState);
			}
		}
		
		/*
		 * havoc all the non-atomic EqNodes which depend on this one
		 */
		if (node instanceof EqAtomicBaseNode) {
			for (EqNonAtomicBaseNode  dependentNode : ((EqAtomicBaseNode) node).getDependentNonAtomicBaseNodes()) {
				resultState = havoc(dependentNode, resultState);
			}
		}
		
		return resultState;
	}
	
	/**
	 * To havoc an array. All the element in this array will be havoc.
	 * 
	 * @param term
	 */
	public VPState<ACTION> havocArray(final IProgramVarOrConst array, VPState<ACTION> originalState) {
		VPState<ACTION> resultState = copy(originalState).build();

		for (final EqFunctionNode fnNode : mDomain.getArrayIdToEqFnNodeMap()
				.getImage(array)) {
			resultState = this.havoc(fnNode, resultState);
		}
		return resultState;
	}

	/**
	 * To havoc a set of nodes. If this set contains array, it will not be havoc
	 * here.
	 * 
	 * @param assignmentVars
	 */
	public VPState<ACTION> havocVariables(final Set<IProgramVar> assignmentVars, VPState<ACTION> originalState) {
		VPState<ACTION> resultState = copy(originalState).build();
		for (final IProgramVar var : assignmentVars) {

			if (var.getTerm().getSort().isArraySort()) {
				resultState = havocArray(var, resultState);
				continue;
			}

			EqNode node = mDomain.getPreAnalysis().getEqNode(var.getTerm(), Collections.emptyMap());
			
			if (node != null) {
				resultState = havoc(node, resultState);
			}
		}
		return resultState;
	}
	
}
