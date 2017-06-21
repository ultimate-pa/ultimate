package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqAtomicBaseNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqGraphNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNonAtomicBaseNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class CongruenceGraph<ACTION extends IIcfgTransition<IcfgLocation>,
		NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
		FUNCTION extends IEqFunctionIdentifier<FUNCTION>> {
	
	private boolean mIsFrozen = false;
	
	private Map<NODE, EqGraphNode<NODE, FUNCTION>> mNodeToEqGraphNode = new HashMap<>();
	
	
	private Set<VPDomainSymmetricPair<NODE>> mDisequalities;

	/**
	 * The EqConstraint that this cGraph belongs to.
	 */
	private final EqConstraint<ACTION, NODE, FUNCTION> mOwningConstraint;
	
	/**
	 * constructs an empty CongruenceGraph
	 */
	public CongruenceGraph(EqConstraint<ACTION, NODE, FUNCTION> owningConstraint) {
//		mNodeToEqGraphNode = new HashMap<>();
		mDisequalities = new HashSet<>();
		mOwningConstraint = owningConstraint;
	}
	
	/**
	 * 
	 */
	public CongruenceGraph(CongruenceGraph<ACTION, NODE, FUNCTION> original) {
		
		mOwningConstraint = original.mOwningConstraint;
		
		// make copies of the EqGraphNodes
		for (Entry<NODE, EqGraphNode<NODE, FUNCTION>> en : original.mNodeToEqGraphNode.entrySet()) {
			final EqGraphNode<NODE, FUNCTION> newEqgn = getOrConstructEqGraphNode(en.getKey());
			final EqGraphNode<NODE, FUNCTION> oldEqgn = en.getValue();
			copyFields(newEqgn, oldEqgn);
		}
		
		// copy the disequality set
		mDisequalities = new HashSet<>(original.mDisequalities);
	}

	private void copyFields(final EqGraphNode<NODE, FUNCTION> newEqgn, final EqGraphNode<NODE, FUNCTION> oldEqgn) {
		copyFields(newEqgn, oldEqgn, null, null);
	}

	/**
	 * 
	 * Copies over the values from the following fields from oldEqgn to newEqgn
	 * <ul>
	 *  <li> representative (also updates reverseRepresentative in the representative)
	 *  <li> ccpar
	 *  <li> ccchild
	 * </ul>
	 *  
	 * initCcpar and initCchild should be set by getOrConstructEqGraphNode and addNode, making for a complete copy
	 * of the EqGraphNode when we need one.
	 * 
	 * @param newEqgn
	 * @param oldEqgn
	 * @param oldNodeToSubstitutedNode 
	 * @param newNodeToEqGraphNodeMap 
	 */
	private void copyFields(final EqGraphNode<NODE, FUNCTION> newEqgn, 
			final EqGraphNode<NODE, FUNCTION> oldEqgn, 
			final Map<NODE, NODE> oldNodeToSubstitutedNode, 
			final Map<NODE, EqGraphNode<NODE, FUNCTION>> newNodeToEqGraphNodeMap) {
		final NODE oldRepresentativeSubstituted;
		if (oldNodeToSubstitutedNode != null) {
			oldRepresentativeSubstituted = oldNodeToSubstitutedNode.get(oldEqgn.getRepresentative().getNode());
			assert oldRepresentativeSubstituted != null;
		} else {
			oldRepresentativeSubstituted = oldEqgn.getRepresentative().getNode();
		}
		
		final EqGraphNode<NODE, FUNCTION> newRepresentative = 
				getOrConstructEqGraphNode(oldRepresentativeSubstituted, newNodeToEqGraphNodeMap);
		newEqgn.setRepresentative(newRepresentative);
		newRepresentative.addToReverseRepresentative(newEqgn);
		newEqgn.setCcpar(new HashSet<>(oldEqgn.getCcpar()));
		newEqgn.setCcchild(new HashRelation<>(oldEqgn.getCcchild()));
	}
	
	/**
	 * This should only be called from "EqState".
	 * Note that this is not symmetric in that the representative of the first node is changed!
	 * 
	 * @param node1
	 * @param node2
	 * @return all node pairs that have been merged during this call and its recursion (no symmetry closure needed)
	 */
	HashRelation<NODE, NODE> merge(NODE node1, NODE node2) {
		assert !mIsFrozen;
		
		final EqGraphNode<NODE, FUNCTION> egn1 = mNodeToEqGraphNode.get(node1);
		final EqGraphNode<NODE, FUNCTION> egn2 = mNodeToEqGraphNode.get(node2);

		if (egn1 == egn2 || egn1.find() == egn2.find()) {
			// nothing to do
			return new HashRelation<>();
		}


		final HashRelation<NODE, NODE> mergeHistory = new HashRelation<>();
		union(egn1, egn2);
		mergeHistory.addPair(node1, node2);

		mergeHistory.addAll(equalityPropagation(egn1, egn2));

		return mergeHistory;
	}
	
	private HashRelation<NODE, NODE> equalityPropagation(final EqGraphNode<NODE, FUNCTION> node1,
			final EqGraphNode<NODE, FUNCTION> node2) {

		final Set<EqGraphNode<NODE, FUNCTION>> p1 = node1.find().getCcpar()
				.stream().map(node -> mNodeToEqGraphNode.get(node)).collect(Collectors.toSet());
		final Set<EqGraphNode<NODE, FUNCTION>> p2 = node2.find().getCcpar()
				.stream().map(node -> mNodeToEqGraphNode.get(node)).collect(Collectors.toSet());

		final HashRelation<NODE, NODE> mergeHistory = new HashRelation<>();
		for (final EqGraphNode<NODE, FUNCTION> t1 : p1) {
			for (final EqGraphNode<NODE, FUNCTION> t2 : p2) {
				if (!(t1.find().equals(t2.find())) && congruent(t1, t2)) {
					mergeHistory.addAll(merge(t1.getNode(), t2.getNode()));
				}
			}
		}
		return mergeHistory;
	}
	
	/**
	 * Check whether @param node1 and @param node2 are congruent.
	 *
	 * @param node1
	 * @param node2
	 * @return true if they are congruent
	 */
	protected boolean congruent(final EqGraphNode<NODE, FUNCTION> node1, final EqGraphNode<NODE, FUNCTION> node2) {
		if (!(node1.mNodeIdentifier.isFunction()) || !(node2.mNodeIdentifier.isFunction())) {
			return false;
		}

		if (!(node1.mNodeIdentifier.getFunction().equals(node2.mNodeIdentifier.getFunction()))) {
			return false;
		}
//		return VPFactoryHelpers.congruentIgnoreFunctionSymbol(node1, node2);
		return congruentIgnoreFunctionSymbol(node1, node2);
	}
	
	public boolean congruentIgnoreFunctionSymbol(
			final EqGraphNode<NODE, FUNCTION> fnNode1, final EqGraphNode<NODE, FUNCTION> fnNode2) {
//			final NODE node1, final NODE node2) {
		// assert fnNode1.getArgs() != null && fnNode2.getArgs() != null;
		// assert fnNode1.getArgs().size() == fnNode2.getArgs().size();
//		assert node1.isFunction();
//		assert node2.isFunction();
		
		for (int i = 0; i < fnNode1.getInitCcchild().size(); i++) {
//		for (int i = 0; i < node1.getArgs().size(); i++) {
//			final EqGraphNode<NODE, FUNCTION> fnNode1Arg = fnNode1.getInitCcchild().get(i);
//			final EqGraphNode<NODE, FUNCTION> fnNode2Arg = fnNode2.getInitCcchild().get(i);
//			final NODE ithArg1 = mNodeToEqGraphNode.get(node1).getInitCcchild().get(i);
//			final NODE ithArg2 = mNodeToEqGraphNode.get(node2).getInitCcchild().get(i);
			final NODE ithArg1 = fnNode1.getInitCcchild().get(i);
			final NODE ithArg2 = fnNode2.getInitCcchild().get(i);
//			if (!fnNode1Arg.find().equals(fnNode2Arg.find())) {
			if (!find(ithArg1).equals(find(ithArg2))) {
				return false;
			}
		}
		return true;
	}
	
		/**
	 * Union of two equivalence classes. The representative of node1 will become the representative of node2.
	 *
	 * @param node1
	 * @param node2
	 */
	protected void union(final EqGraphNode<NODE, FUNCTION> node1, final EqGraphNode<NODE, FUNCTION> node2) {
		
//		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisEqualitySet, this);

		if (node1.find().equals(node2.find())) {
			assert false : "this should have been checked before calling union";
			return;
		}
		
		final EqGraphNode<NODE, FUNCTION> oldNode1Representative = node1.find();
		
		node2.find().addToReverseRepresentative(node1.find());
		node2.find().addToCcpar(node1.find().getCcpar());
		node2.find().addToCcchild(node1.find().getCcchild());
		// this set-operation must come after the other 3 above (because find is called on node1 for all the others)!!
		node1.find().setRepresentative(node2.find());

//		assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisequalities, this);

		/*
		 * Because node1.find has a new representative, any disequality that contains its old representative must be
		 * updated to its new representative
		 *
		 */
		final Set<VPDomainSymmetricPair<NODE>> copyOfDisEqSet = new HashSet<>(mDisequalities);
		for (final VPDomainSymmetricPair<NODE> pair : copyOfDisEqSet) {
			final EqGraphNode<NODE, FUNCTION> firstEqnInDisEquality = getEqGraphNode(pair.getFirst());
			final EqGraphNode<NODE, FUNCTION> secondEqnInDisEquality = getEqGraphNode(pair.getSecond());

			if (firstEqnInDisEquality != oldNode1Representative && secondEqnInDisEquality != oldNode1Representative) {
				// pair does not contain node1's old representative
				continue;
			}
			
			NODE newFirst = pair.getFirst();
			NODE newSecond = pair.getSecond();
			
			if (firstEqnInDisEquality == oldNode1Representative) {
				newFirst = node1.find().mNodeIdentifier;
			}
			if (secondEqnInDisEquality == oldNode1Representative) {
				newSecond = node1.find().mNodeIdentifier;
			}

			mDisequalities.remove(pair);
			mDisequalities.add(new VPDomainSymmetricPair<NODE>(newFirst, newSecond));
//			assert VPDomainHelpers.disEqualityRelationIrreflexive(this.mDisEqualitySet, this); // this may happen if, 
																						//in fact, we have a conflict
		}

//		assert VPDomainHelpers.disEqualitySetContainsOnlyRepresentatives(mDisequalities, this);
	}

	private EqGraphNode<NODE, FUNCTION> getEqGraphNode(NODE node) {
		return mNodeToEqGraphNode.get(node);
	}

	/**
	 * Returns the representative node of the given node in the current congruence graph.
	 * Returns null if the given node does not exist in the graph.
	 * 
	 * @param node
	 * @return representative or null
	 */
	public NODE find(NODE node) {
		EqGraphNode<NODE, FUNCTION> egn = mNodeToEqGraphNode.get(node);
		if (egn == null) {
			return null;
		}
		return egn.find().getNode();
	}
	
	/**
	 * To havoc a node. There are three main parts to handle:
	 * <ol>
	 *  <li> Handling the outgoing edge chain. 
	 *  <li> Handling the incoming edges. 
	 *  <li> Handling the node itself.
	 * </ol>
	 *
	 * @param nodeToBeHavocced EqGraphNode to be havocced
	 * @param originalState
	 * @return 
	 */
	public void havoc(NODE nodeToBeHavocced) {
		assert !mIsFrozen;

		assert !nodeToBeHavocced.isLiteral() : "cannot havoc a literal";

		
		EqGraphNode<NODE, FUNCTION> graphNodeForNodeToBeHavocced = mNodeToEqGraphNode.get(nodeToBeHavocced);

		// TODO: determine if state becomes top through the havoc!

		/*
		 * 1. Handling the outgoing edge chain
		 * 
		 *  <li> sever the outgoing edge from nodeToBeHavocced
		 *  <li> update ccchild and ccpar entries in each of the transitive representatives of the havocced node
		 *  <li>  Remember that the ccchild and ccpar entries of each node represent the history of those fields, i.e.,
		 *      the ccchild/par when that node was a representative
		 *  <li> for each of the transitive representatives we build the set difference
		 */
		final EqGraphNode<NODE, FUNCTION> firstRepresentative =
				graphNodeForNodeToBeHavocced.getRepresentative();
		EqGraphNode<NODE, FUNCTION> nextRepresentative = firstRepresentative;
		// remove the outgoing equality edge from the nodeToBeHavocced
		nextRepresentative.getReverseRepresentative().remove(graphNodeForNodeToBeHavocced);
		while (!(nextRepresentative.equals(nextRepresentative.getRepresentative()))) {
			nextRepresentative.getCcpar().removeAll(graphNodeForNodeToBeHavocced.getCcpar());
			nextRepresentative.getCcchild().removeAllPairs(graphNodeForNodeToBeHavocced.getCcchild());
			nextRepresentative = nextRepresentative.getRepresentative();
		}
		assert nextRepresentative != graphNodeForNodeToBeHavocced : "do we need a special case, here?";
		// one more step is needed for the last element of the representative chain
		nextRepresentative.removeFromCcpar(graphNodeForNodeToBeHavocced.getCcpar());
		nextRepresentative.removeFromCcchild(graphNodeForNodeToBeHavocced.getCcchild());

		/*
		 * 2. Handling the incoming edges (reverseRepresentative). Point nodes in reverseRepresentative to the
		 * representative of the node that is being havoc. For example, y -> x -> z. Havoc x, then we have y -> z But if
		 * the node that is being havoc is its own representative, then point nodes in reverseRepresentative to one of
		 * them. For example, y -> x <- z, Havoc x, then we have y -> z or z -> y.
		 */
		EqGraphNode<NODE, FUNCTION> firstReverseRepresentativeNode = null;
		if (!graphNodeForNodeToBeHavocced.getReverseRepresentative().isEmpty()) {
			firstReverseRepresentativeNode = graphNodeForNodeToBeHavocced.getReverseRepresentative().iterator().next();
		}
		for (final EqGraphNode<NODE, FUNCTION> reverseNode : graphNodeForNodeToBeHavocced
				.getReverseRepresentative()) {
			// first reset the representative of all the reverseRepresentative nodes.
			reverseNode.setRepresentative(reverseNode);
		}
		
		/*
		 * we have to reconnect nodes that were connected through an equality chain that contained the nodeToBeHavocced
		 */
		boolean havocNodeWasItsRepresentativeBeforeHavoc = false;
		for (final EqGraphNode<NODE, FUNCTION> reverseNode : graphNodeForNodeToBeHavocced
				.getReverseRepresentative()) {
			// case y -> x <- z
			if (firstRepresentative.equals(graphNodeForNodeToBeHavocced)) {
				havocNodeWasItsRepresentativeBeforeHavoc = true;
				if (graphNodeForNodeToBeHavocced.getReverseRepresentative().size() > 1) {
					assert firstReverseRepresentativeNode != null;
					merge(reverseNode.getNode(), firstRepresentative.getNode());
					
				}
			} else { // case y -> x -> z
				merge(reverseNode.getNode(), firstRepresentative.getNode());
			}
		}
		
//		final VPStateBuilder<ACTION> builder2 = copy(resultState);
//		graphNodeForNodeToBeHavocced = builder2.getEqGraphNode(nodeToBeHavocced);
		
		/*
		 * 3. Handling the nodeToBeHavocced itself: First update disequality set. Then set nodeToBeHavocced to initial.
		 */
		if (havocNodeWasItsRepresentativeBeforeHavoc) {
			/*
			 *  nodeToBehavocced was the representative of an equivalence class --> we need to 
			 */
			final Set<VPDomainSymmetricPair<NODE>> newDisEqualitySet = new HashSet<>();
			for (final VPDomainSymmetricPair<NODE> pair : getDisequalities()) {
				if (pair.contains(graphNodeForNodeToBeHavocced.mNodeIdentifier)) {
					newDisEqualitySet.add(new VPDomainSymmetricPair<NODE>(
							pair.getOther(nodeToBeHavocced),
							find(firstReverseRepresentativeNode.getNode())));
				} else {
					newDisEqualitySet.add(pair);
				}
			}
			mDisequalities = newDisEqualitySet;
		} else {
			// do nothing: no need to update disequality set, because if x is not representative, then x should not be
			// in disequality set.
		}
		graphNodeForNodeToBeHavocced.setNodeToInitial();

		/*
		 * 
		 */
		if (nodeToBeHavocced.isFunction()) {
			restorePropagation(nodeToBeHavocced);
		}
		
		/*
		 * havoc the function nodes which nodeToBeHavocced was an index of
		 */
		if (!graphNodeForNodeToBeHavocced.getInitCcpar().isEmpty()) {
			for (final NODE initCcpar : graphNodeForNodeToBeHavocced.getInitCcpar()) {
				havoc(initCcpar);
			}
		}
		
		/*
		 * havoc all the non-atomic EqNodes which depend on this one
		 */
		if (nodeToBeHavocced instanceof EqAtomicBaseNode) {
			for (final EqNonAtomicBaseNode dependentNode : ((EqAtomicBaseNode) nodeToBeHavocced)
					.getDependentNonAtomicBaseNodes()) {
				havoc((NODE) dependentNode);
			}
		}
		
		mOwningConstraint.removeNode(nodeToBeHavocced);
	}
	
	
	/**
	 * An additional process after a function node is havoc, in order to restore the propagation.
	 * For example, we have two nodes a[i] and a[j], if i = j, by equality propagation,
	 * we also know a[i] = a[j]. When a[i] is being havoc, we lose the information of a[i] = a[j],
	 * which is the result of equality propagation of (i = j). This method is to restore this
	 * information.
	 *
	 * @param functionNode
	 */
	 private void restorePropagation(final NODE functionNode) {
		 assert functionNode.isFunction();
	
		 NODE firstIndex = functionNode.getArgs().get(0);
		 
		 EqGraphNode<NODE, FUNCTION> firstIndexGN = mNodeToEqGraphNode.get(firstIndex);

		 final Set<NODE> fnNodesWithSameFunction = getFunctionNodesForFunctionSymbol(functionNode.getFunction());
		 for (final NODE fnNode : fnNodesWithSameFunction) {
			 if (mNodeToEqGraphNode.get(fnNode.getArgs().get(0)).find().equals(firstIndexGN.find())) {
				 if (congruent(mNodeToEqGraphNode.get(fnNode), mNodeToEqGraphNode.get(functionNode))) {
					 merge(fnNode, functionNode);
				 }
			 }
		 }
	 }
	
	private Set<NODE> getFunctionNodesForFunctionSymbol(FUNCTION function) {
		// TODO: cache?
		return mNodeToEqGraphNode.keySet().stream()
			.filter(node -> (node.isFunction() && node.getFunction().equals(function)))
			.collect(Collectors.toSet());
	}

	/**
	 * Use disEqualitySet to check if there exist contradiction in the graph.
	 *
	 * @return true if there is contradiction
	 */
	boolean checkContradiction() {
		
		for (final VPDomainSymmetricPair<NODE> disEqPair : mDisequalities) {
			if (getEqGraphNode(disEqPair.getFirst()).find().equals(getEqGraphNode(disEqPair.getSecond()).find())) {
				return true;
			}
		}
		return false;
	}
	
	public void freeze() {
		assert !mIsFrozen;

		mIsFrozen = true;
	}

	public Set<VPDomainSymmetricPair<NODE>> getDisequalities() {
		return mDisequalities;
	}

	public void renameVariables(Map<Term, Term> substitutionMapping) {
		assert !mIsFrozen;
		
		final Map<NODE, NODE> oldNodeToSubstitutedNode = new HashMap<>();
		for (NODE oldNode : mNodeToEqGraphNode.keySet()) {
			oldNodeToSubstitutedNode.put(oldNode, oldNode.renameVariables(substitutionMapping));
		}
		
		final Map<NODE, EqGraphNode<NODE, FUNCTION>> newNodeToEqGraphNodeMap = new HashMap<>();
		
		for (Entry<NODE, EqGraphNode<NODE, FUNCTION>> en : mNodeToEqGraphNode.entrySet()) {
			final NODE newNode = oldNodeToSubstitutedNode.get(en.getKey());
			final EqGraphNode<NODE, FUNCTION> newEqgn = getOrConstructEqGraphNode(newNode, newNodeToEqGraphNodeMap);
			copyFields(newEqgn, en.getValue(), oldNodeToSubstitutedNode, newNodeToEqGraphNodeMap);
			
//			newNodeToEqGraphNodeMap.put(newNode, newEqgn);
		}

		mNodeToEqGraphNode = newNodeToEqGraphNodeMap;
		
		final Set<VPDomainSymmetricPair<NODE>> newDisequalities = new HashSet<>();
		
		for (VPDomainSymmetricPair<NODE> deq : mDisequalities) {
			newDisequalities.add(new VPDomainSymmetricPair<NODE>(oldNodeToSubstitutedNode.get(deq.getFirst()),
					oldNodeToSubstitutedNode.get(deq.getSecond())));
		}
		mDisequalities = newDisequalities;
	}

	public void addDisequality(NODE find, NODE find2) {
		mDisequalities.add(new VPDomainSymmetricPair<NODE>(find, find2));
	}
	


//	public void addNodes(Collection<NODE> allNodes) {
//		// TOD Auto-generated method stub
//		assert false;
//	}

	/**
	 * Add a node to the congruence graph.
	 * This does not do any propagations but may allow some.
	 * @param node
	 * @param initCCpar the parent node, use null for 'no parent'
	 */
	public void addNode(NODE node, NODE initCCpar) {
		if (mNodeToEqGraphNode.containsKey(node)) {
			final EqGraphNode<NODE, FUNCTION> eqgn = mNodeToEqGraphNode.get(node);
//			if (initCCpar != null && eqgn.getInitCcpar().isEmpty()) {
			if (initCCpar != null && eqgn.getInitCcpar() != null) {
				eqgn.addToInitCcpar(initCCpar);
			}
			return;
		}
		
		if (node.isFunction()) {
			for (NODE child : node.getArgs()) {
				addNode(child, node);
			}
		}
		
		final EqGraphNode<NODE, FUNCTION> eqgn = getOrConstructEqGraphNode(node);//new EqGraphNode<NODE, FUNCTION>(node);
		if (initCCpar != null) {
			eqgn.addToInitCcpar(initCCpar);
		}
		
		mNodeToEqGraphNode.put(node, eqgn);
	}

	/**
	 * version that updates mNodeToEqGraphNodeMap
	 * @param node
	 * @return
	 */
	private EqGraphNode<NODE, FUNCTION> getOrConstructEqGraphNode(NODE node) {
		return getOrConstructEqGraphNode(node, null);
	}

	/**
	 * version that updates the given map, mNodeToEqGraphNodeMap only if the given map is null
	 * @param node
	 * @param newNodeToEqGraphNodeMap
	 * @return
	 */
	private EqGraphNode<NODE, FUNCTION> getOrConstructEqGraphNode(NODE node, Map<NODE, 
			EqGraphNode<NODE, FUNCTION>> newNodeToEqGraphNodeMap) {
		EqGraphNode<NODE, FUNCTION> result;
		if (newNodeToEqGraphNodeMap == null) {
			result = mNodeToEqGraphNode.get(node);
		} else {
			result = newNodeToEqGraphNodeMap.get(node);
		}

		if (result == null) {
			result = new EqGraphNode<>(node);
			if (node.isFunction()) {
				for (NODE child : result.getInitCcchild()) {
					final EqGraphNode<NODE, FUNCTION> childEqgn = getOrConstructEqGraphNode(child, 
							newNodeToEqGraphNodeMap);
//					if (childEqgn.getInitCcpar().contains(node)) {
						childEqgn.addToInitCcpar(node);
//					} else {
////						assert childEqgn.getInitCcpar().size() == 1 
////								&& childEqgn.getInitCcpar().iterator().next() == node;
//						assert childEqgn.getInitCcpar() == node;
//					}
				}
			}
			if (newNodeToEqGraphNodeMap == null) {
				mNodeToEqGraphNode.put(node, result);
			} else {
				newNodeToEqGraphNodeMap.put(node, result);
			}
		}
		return result;
	}

	public HashRelation<FUNCTION, List<NODE>> getCCChild(NODE representative1) {
		return mNodeToEqGraphNode.get(representative1).getCcchild();
	}

	public HashRelation<NODE, NODE> getSupportingEqualities() {
		final HashRelation<NODE, NODE> result = new HashRelation<>();

		for (NODE node : mNodeToEqGraphNode.keySet()) {
			NODE representative = find(node);
			if (representative != node) {
				result.addPair(node, representative);
			}
		}
		
		return result;
	}
	
	@Override
	public String toString() {
		return String.format("Nodes: %s \n Disequalities: %s", mNodeToEqGraphNode, mDisequalities);
	}
}
