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
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class VPStateFactory implements IVPFactory<VPState>{
	
	private final VPDomain mDomain;
//	private final VPStateBottom mBottomState;
	private final Map<Set<IProgramVar>, VPStateBottom> mBottomStates = new HashMap<>();

	public VPStateFactory(VPDomain vpdomain) {
		mDomain = vpdomain;
//		mBottomState = new VPStateBottom(vpdomain);
	}
	
	public VPStateBuilder createEmptyStateBuilder() {
		
		VPStateBuilder builder = new VPStateBuilder(mDomain);
		
		/*
		 * When all EqGraphNodes for the VPState have been created, we can set their
		 * initCcpar and initCcchild fields
		 */
		for (EqGraphNode egn : builder.getEqNodeToEqGraphNodeMap().values()) {
			egn.setupNode();
		}
		
		/*
		 * Generate disequality set for constants
		 */
		Set<VPNodeIdentifier> literalSet = mDomain.getLiteralEqNodes()
				.stream()
				.map(eqNode -> new VPNodeIdentifier(eqNode))
				.collect(Collectors.toSet());
		Set<VPDomainSymmetricPair<VPNodeIdentifier>> disEqualitySet = new HashSet<>();
		for (VPNodeIdentifier node1 : literalSet) {
			for (VPNodeIdentifier node2 : literalSet) {
				if (!node1.equals(node2)) {
					disEqualitySet.add(new VPDomainSymmetricPair<>(node1, node2));
				}
			}
		}
		builder.addDisEqualites(disEqualitySet);
		
		/*
		 * The set of tracked variables (as exposed to the fixpointengine) is empty, initially.
		 */
		Set<IProgramVar> vars = new HashSet<>();
		builder.setVars(vars);

		builder.setIsTop(true);

		return builder;
	}
	
	public VPStateBottom getBottomState(Set<IProgramVar> set) {
		VPStateBottom result = mBottomStates.get(set);
		if (result == null) {
			VPStateBottomBuilder builder = new VPStateBottomBuilder(mDomain);
			builder.addVariables(set);
			result = builder.build();
			mBottomStates.put(set, result);
		}
		return result;
	}
	
	public VPState getTopState(Set<IProgramVar> vars) {
		return createEmptyStateBuilder().setVars(vars).build();
	}

	public VPStateBuilder translateForTransFormula(VPState originalState, 
			Map<IProgramVar, TermVariable> inVars,
			Map<IProgramVar, TermVariable> outVars,
			Set<TermVariable> auxVars) {
		//TODO
		return null;
	}

	public VPStateBuilder copy(VPState originalState) {
		if (originalState.isBottom()) {
			return new VPStateBottomBuilder(mDomain).setVars(originalState.getVariables());
		}
		
		final VPStateBuilder builder = createEmptyStateBuilder();
		
		for (EqNode eqNode : mDomain.getTermToEqNodeMap().values()) {
			EqGraphNode newGraphNode = builder.getEqNodeToEqGraphNodeMap().get(eqNode);
			EqGraphNode oldGraphNode = originalState.getEqNodeToEqGraphNodeMap().get(eqNode);
			newGraphNode.copyFields(oldGraphNode, builder.getEqNodeToEqGraphNodeMap());
			assert !originalState.isTop() || newGraphNode.getRepresentative() == newGraphNode;
		}
		
		for (VPDomainSymmetricPair<VPNodeIdentifier> pair : originalState.getDisEqualities()) {
			builder.addDisEquality(pair);
			assert !originalState.isTop() || (pair.mFst.isLiteral() && pair.mSnd.isLiteral()) : 
				"The only disequalites in a top state are between constants";
		}
		
		builder.setVars(new HashSet<>(originalState.getVariables()));
		
		builder.setIsTop(originalState.isTop());

		assert builder.mVars.equals(originalState.getVariables());
		return builder;
	}

//	/**
//	 * To havoc a node. There are three main parts to handle: (1) Handling the
//	 * outgoing edge chain. (2) Handling the incoming edges. (3) Handling the
//	 * node itself.
//	 * 
//	 * @param EqGraphNode
//	 *            to be havoc
//	 */
//	public VPState havoc(final EqNode node, final VPState originalState) {
//		if (originalState.isBottom()) {
//			return originalState;
//		}
//		
//		//assert !node.isLiteral() : "cannot havoc a literal";
//		assert node.getTerm(mDomain.getManagedScript()).getFreeVars().length > 0 : "cannot havoc a constant term";
//		
//		
//		VPStateBuilder builder = copy(originalState);
//		EqGraphNode graphNode = builder.getEqNodeToEqGraphNodeMap().get(node);
//		
//		// TODO: determine if state becomes top through the havoc!
//
//		// Handling the outgoing edge chain
//		final EqGraphNode firstRepresentative = graphNode.getRepresentative();
//		EqGraphNode nextRepresentative = firstRepresentative;
//		nextRepresentative.getReverseRepresentative().remove(graphNode);
//		while (!(nextRepresentative.equals(nextRepresentative.getRepresentative()))) {
//			nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
//			for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode.getCcchild().entrySet()) {
//				nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
//			}
//			nextRepresentative = nextRepresentative.getRepresentative();
//		}
//		nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
//		HashRelation<IProgramVarOrConst, List<EqGraphNode>> copyOfGraphNodeCcchild = new HashRelation<>();
//		for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode.getCcchild().entrySet()) {
//			copyOfGraphNodeCcchild.addPair(entry.getKey(), entry.getValue());
//		}
//		for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : copyOfGraphNodeCcchild.entrySet()) {
//			nextRepresentative.getCcchild().removePair(entry.getKey(), entry.getValue());
//		}
//
//		/*
//		 *  Handling the incoming edges (reverseRepresentative).
//		 *  Point nodes in reverseRepresentative to the representative of the node that is being havoc.
//		 *  For example, y -> x -> z. Havoc x, then we have y -> z
//		 *  But if the node that is being havoc is its own representative, 
//		 *  then point nodes in reverseRepresentative to one of them.
//		 *  For example, y -> x <- z, Havoc x, then we have y -> z or z -> y.
//		 */
//		EqGraphNode firstReserveRepresentativeNode = null;
//		if (!graphNode.getReverseRepresentative().isEmpty()) {
//			firstReserveRepresentativeNode = graphNode.getReverseRepresentative().iterator().next();
//		}
//		for (final EqGraphNode reverseNode : graphNode.getReverseRepresentative()) {
//			// first reset the representative of all the reverseRepresentative nodes.
//			reverseNode.setRepresentative(reverseNode);
//		}
//		
//		boolean havocNodeIsItsRepresentative = false;
//		VPState resultState = builder.build();
//		for (final EqGraphNode reverseNode : graphNode.getReverseRepresentative()) {
//			// case y -> x <- z
//			if (firstRepresentative.equals(graphNode)) {
//				havocNodeIsItsRepresentative = true;
//				if (graphNode.getReverseRepresentative().size() > 1) {
//					assert firstReserveRepresentativeNode != null;
//					resultState = disjoinAll(addEquality(reverseNode.eqNode, firstReserveRepresentativeNode.eqNode, resultState));
//				}
//			} else { // case y -> x -> z
//				resultState = disjoinAll(addEquality(reverseNode.eqNode, firstRepresentative.eqNode, resultState));
//			}
//		}
//		
//		builder = copy(resultState);
//		graphNode = builder.getEqNodeToEqGraphNodeMap().get(node);
//		
//		/*
//		 * Handling the node itself:
//		 * First update disequality set.
//		 * Then set havoc node to initial.
//		 */
//		if (havocNodeIsItsRepresentative) {
//			Set<VPDomainSymmetricPair<EqNode>> newDisEqualitySet = new HashSet<>();
//			for (VPDomainSymmetricPair<EqNode> pair : builder.getDisEqualitySet()) {
//				if (pair.contains(graphNode.eqNode)) {
//					newDisEqualitySet.add(
//							new VPDomainSymmetricPair<EqNode>(pair.getOther(graphNode.eqNode), resultState.find(firstReserveRepresentativeNode).eqNode));
//				} else {
//					newDisEqualitySet.add(pair);
//				}
//			}
//			builder.setDisEqualites(newDisEqualitySet);
//		} else {
//			// do nothing: no need to update disequality set, because if x is not representative, then x should not be in disequality set.
//		}
////		if (graphNode.getRepresentative().equals(graphNode)) {
////			Set<VPDomainSymmetricPair<EqNode>> newSet = 
////					builder.getDisEqualitySet().stream()
////					.filter(pair -> !pair.contains(node))
////					.collect(Collectors.toSet());
////			builder.setDisEqualites(newSet);
////		}
//		graphNode.setNodeToInitial();
//
//		if (node instanceof EqFunctionNode) {
//			builder.restorePropagation((EqFunctionNode) node);
//		}
//		resultState = builder.build();
//		
//		// also havoc the function nodes which index had been havoc.
//		if (!graphNode.getInitCcpar().isEmpty()) {
//			for (final EqGraphNode initCcpar : graphNode.getInitCcpar()) {
//				resultState = havoc(initCcpar.eqNode, resultState);
//			}
//		}
//		
//		/*
//		 * havoc all the non-atomic EqNodes which depend on this one
//		 */
//		if (node instanceof EqAtomicBaseNode) {
//			for (EqNonAtomicBaseNode  dependentNode : ((EqAtomicBaseNode) node).getDependentNonAtomicBaseNodes()) {
//				resultState = havoc(dependentNode, resultState);
//			}
//		}
//		
//		return resultState;
//	}
//	
//	/**
//	 * To havoc an array. All the element in this array will be havoc.
//	 * 
//	 * @param term
//	 */
//	public VPState havocArray(final IProgramVarOrConst array, VPState originalState) {
//		VPState resultState = copy(originalState).build();
//
//		for (final EqFunctionNode fnNode : mDomain.getArrayIdToEqFnNodeMap()
//				.getImage(array)) {
//			resultState = this.havoc(fnNode, resultState);
//		}
//		return resultState;
//	}
//
//	/**
//	 * To havoc a set of nodes. If this set contains array, it will not be havoc
//	 * here.
//	 * 
//	 * @param assignmentVars
//	 */
//	public VPState havocVariables(final Set<IProgramVar> assignmentVars, VPState originalState) {
//		VPState resultState = copy(originalState).build();
//		for (final IProgramVar var : assignmentVars) {
//
//			if (var.getTerm().getSort().isArraySort()) {
//				resultState = havocArray(var, resultState);
//				continue;
//			}
//
//			EqNode node = mDomain.getPreAnalysis().getEqNode(var.getTerm(), Collections.emptyMap());
//			
//			if (node != null) {
//				resultState = havoc(node, resultState);
//			}
//		}
//		return resultState;
//	}
//	
//
//	public Set<VPState> havoc(EqNode node, Set<VPState> states) {
//		Set<VPState> result = new HashSet<>();
//		for (VPState state : states) {
//			result.add(havoc(node, state));
//		}
//		return result;
//	}
//
//	public Set<VPState> havocArray(IProgramVar key, Set<VPState> resultStates) {
//		Set<VPState> result = new HashSet<>();
//		for (VPState state : resultStates) {
//			result.add(havocArray(key, state));
//		}
//		return result;
//	}

	/**
	 * Takes a set of TransitionStates (VPTfState) and a TransFormula. Converts the transition-states to 
	 * normal states (VPState), essentially by projecting the transition state to the outVars of the given
	 * TransFormula.
	 * 
	 * @param resultTfStates
	 * @param tf
	 * @return
	 */
	public Set<VPState> convertToStates(Set<VPTfState> tfStates, UnmodifiableTransFormula tf) {
		Set<VPState> result = new HashSet<>();
		
		for (VPTfState tfState : tfStates)  {
			result.add(convertToState(tfState, tf));
		}
		
		return result;
	}

	/*
	 * (first) plan:
	 *  for every two outVars, query which (dis-)equalities hold for them
	 * TODO: naive (quadratic) implementation
	 * in the future perhaps: work on the graph directly
	 */
	private VPState convertToState(VPTfState tfState, UnmodifiableTransFormula tf) {
		if (tfState.isBottom()) {
			return getBottomState(tfState.getVariables());
		}
		
		if (tfState.isTop()) {
			VPStateBuilder builder = createEmptyStateBuilder();
			builder.addVariables(tfState.getVariables());
			return builder.build();
		}
		
		VPStateBuilder builder = createEmptyStateBuilder();
		builder.setVars(tfState.getVariables());
		builder.setIsTop(true);

		for (Entry<IProgramVar, TermVariable> outVar1 : tf.getOutVars().entrySet()) {
			for (Entry<IProgramVar, TermVariable> outVar2 : tf.getOutVars().entrySet()) {
				if (outVar1.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				EqNode eqNodeForOutVar1 = 
						mDomain.getPreAnalysis().getEqNode(outVar1.getKey().getTerm(), Collections.emptyMap());
				EqNode eqNodeForOutVar2 = 
						mDomain.getPreAnalysis().getEqNode(outVar2.getKey().getTerm(), Collections.emptyMap());
				assert eqNodeForOutVar1 != null;
				assert eqNodeForOutVar2 != null;
				VPNodeIdentifier id1 = new VPNodeIdentifier(eqNodeForOutVar1);
				VPNodeIdentifier id2 = new VPNodeIdentifier(eqNodeForOutVar2);
				if (tfState.areUnEqual(id1, id2)) {
					builder.addDisEquality(id1, id2);
					builder.setIsTop(false);
				}
			}
		}
		
		VPState stateWithDisEqualitiesAdded = builder.build();
		
		Set<VPState> resultStates = new HashSet<>();
		resultStates.add(stateWithDisEqualitiesAdded);
		
		for (Entry<IProgramVar, TermVariable> outVar1 : tf.getOutVars().entrySet()) {
			for (Entry<IProgramVar, TermVariable> outVar2 : tf.getOutVars().entrySet()) {
				if (outVar1.getKey().getTerm().getSort().isArraySort()) {
					continue;
				}
				EqNode eqNodeForOutVar1 = 
						mDomain.getPreAnalysis().getEqNode(outVar1.getKey().getTerm(), Collections.emptyMap());
				EqNode eqNodeForOutVar2 = 
						mDomain.getPreAnalysis().getEqNode(outVar2.getKey().getTerm(), Collections.emptyMap());
				assert eqNodeForOutVar1 != null;
				assert eqNodeForOutVar2 != null;
				VPNodeIdentifier id1 = new VPNodeIdentifier(eqNodeForOutVar1);
				VPNodeIdentifier id2 = new VPNodeIdentifier(eqNodeForOutVar2);
				if (tfState.areEqual(id1, id2)) {
					resultStates = VPFactoryHelpers.addEquality(id1, id2, resultStates, this);
					builder.setIsTop(false);
				}
			}
		}
		
		assert resultStates.size() == 1 : "??";
		return resultStates.iterator().next();
	}

	@Override
	public Set<VPNodeIdentifier> getFunctionNodesForArray(VPState state, VPArrayIdentifier firstArray) {
		return getFunctionNodesForArray(firstArray);
	}

	public Set<VPNodeIdentifier> getFunctionNodesForArray(VPArrayIdentifier firstArray) {
		assert firstArray.mPvoc != null;
		Set<EqFunctionNode> image = mDomain.getArrayIdToEqFnNodeMap().getImage(firstArray.mPvoc);
		return image.stream().map(node -> new VPNodeIdentifier(node)).collect(Collectors.toSet());
	}

	public VPState disjoinAll(Set<VPState> statesForCurrentEc) {
		return VPFactoryHelpers.disjoinAll(statesForCurrentEc, this);
	}
}
