/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.vp;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPState implements IAbstractState<VPState, CodeBlock, IProgramVar> {

	private final Set<IProgramVar> mVars;

	private final Set<EqGraphNode> mEqGraphNodeSet;
	private final Map<Term, EqBaseNode> mTermToBaseNodeMap;
	private final Map<Term, Set<EqFunctionNode>> mTermToFnNodeMap;
	private final Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;

	private Set<VPDomainSymmetricPair<EqNode>> mDisEqualitySet;
	
	private final VPDomain mDomain;

	public Set<EqGraphNode> getEqGraphNodeSet() {
		return mEqGraphNodeSet;
	}

	public Map<Term, EqBaseNode> getTermToBaseNodeMap() {
		return mTermToBaseNodeMap;
	}

	public Map<Term, Set<EqFunctionNode>> getTermToFnNodeMap() {
		return mTermToFnNodeMap;
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		return mEqNodeToEqGraphNodeMap;
	}

	public Set<VPDomainSymmetricPair<EqNode>> getDisEqualitySet() {
		return mDisEqualitySet;
	}

	public void setDisEqualitySet(Set<VPDomainSymmetricPair<EqNode>> disEqualitySet) {
		this.mDisEqualitySet = disEqualitySet;
	}
	
	VPState() {
		this(null, null, null, null, null, null);
	}
	
	VPState(Set<EqGraphNode> eqGraphNodeSet, Map<Term, EqBaseNode> termToBaseNodeMap,
			Map<Term, Set<EqFunctionNode>> termToFnNodeMap, Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap,
			Set<VPDomainSymmetricPair<EqNode>> disEqualitySet, VPDomain domain) {
		mVars = new HashSet<IProgramVar>();
		mEqGraphNodeSet = eqGraphNodeSet == null ? null : Collections.unmodifiableSet(eqGraphNodeSet);
		mTermToBaseNodeMap = termToBaseNodeMap == null ? null : Collections.unmodifiableMap(termToBaseNodeMap);
		mTermToFnNodeMap = termToFnNodeMap == null ? null : Collections.unmodifiableMap(termToFnNodeMap);
		mEqNodeToEqGraphNodeMap = eqNodeToEqGraphNodeMap;
		mDisEqualitySet = disEqualitySet;
		mDomain = domain;
	}

	/**
	 * This is a pre-step before deriving a new @VPState with @CodeBlock
	 * (transition) in order to handle assignment and assume in the same way. In
	 * this method, the variables that are about to be assigned will be havoc
	 * first. Then the graph will be change and return a new @VPState with the
	 * new graph.
	 * 
	 * @param assignmentVars
	 * @return a state that the assignment vars are being havoc.
	 */
	public VPState prepareState(final Set<IProgramVar> assignmentVars) {

		VPState preparedState = this.copy();
		preparedState.havocBaseNode(assignmentVars);

		return preparedState;
	}

	/**
	 * To havoc a set of nodes. If this set contains array, it will not be havoc
	 * here.
	 * 
	 * @param assignmentVars
	 */
	private void havocBaseNode(final Set<IProgramVar> assignmentVars) {

		TermVariable tv;

		for (final IProgramVar var : assignmentVars) {

			tv = var.getTermVariable();
			if (isArray(tv)) {
				continue;
			}

			if (mTermToBaseNodeMap.containsKey(tv)) {
				assert mEqNodeToEqGraphNodeMap.containsKey(mTermToBaseNodeMap.get(tv));
				havoc(mTermToBaseNodeMap.get(tv));
			}
		}
	}

	/**
	 * To havoc an array. All the element in this array will be havoc.
	 * 
	 * @param term
	 */
	private void havocArray(final Term term) {

		assert mTermToFnNodeMap.containsKey(term);

		for (final EqFunctionNode fnNode : mTermToFnNodeMap.get(term)) {
			havoc(fnNode);
		}
	}

	/**
	 * To havoc a node. There are three main parts to handle: (1) Handling the
	 * outgoing edge chain. (2) Handling the incoming edges. (3) Handling the
	 * node itself.
	 * 
	 * @param node
	 *            to be havoc
	 */
	public void havoc(final EqNode node) {

		assert mEqNodeToEqGraphNodeMap.containsKey(node);
		EqGraphNode graphNode = mEqNodeToEqGraphNodeMap.get(node);

		// Handling the outgoing edge chain
		EqGraphNode nextRepresentative = mEqNodeToEqGraphNodeMap.get(graphNode.getRepresentative());
		nextRepresentative.getReverseRepresentative().remove(node);
		while (!(nextRepresentative.eqNode.equals(nextRepresentative.getRepresentative()))) {
			nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
			nextRepresentative.getCcchild().removeAll(graphNode.getCcchild());
			nextRepresentative = mEqNodeToEqGraphNodeMap.get(nextRepresentative.getRepresentative());
		}
		nextRepresentative.getCcpar().removeAll(graphNode.getCcpar());
		nextRepresentative.getCcchild().removeAll(graphNode.getCcchild());

		// Handling the incoming edges
		for (final EqNode reverseNode : graphNode.getReverseRepresentative()) {
			mEqNodeToEqGraphNodeMap.get(reverseNode).setRepresentative(reverseNode);
		}

		// Handling the node itself
		graphNode.setNodeToInitial();
		for (final VPDomainSymmetricPair<EqNode> disEqPair : mDisEqualitySet) {
			if (disEqPair.getFirst().equals(graphNode.eqNode)) {
				mDisEqualitySet.remove(disEqPair);
			} else if (disEqPair.getSecond().equals(graphNode.eqNode)) {
				mDisEqualitySet.remove(disEqPair);
			}
		}
		
		if (node instanceof EqFunctionNode) {
			restorePropagation((EqFunctionNode)node);
		}
		
		// also havoc the function nodes which index had been havoc.
		if (!graphNode.getInitCcpar().isEmpty()) {
			for (final EqNode initCcpar : graphNode.getInitCcpar()) {
				havoc(initCcpar);
			}
		}
	}

	private void restorePropagation(final EqFunctionNode node) {
		final Set<EqFunctionNode> fnNodeSet = mTermToFnNodeMap.get(node.term);
		for (final EqFunctionNode fnNode1: fnNodeSet) {
			for (final EqFunctionNode fnNode2: fnNodeSet) {
				if (!fnNode1.equals(fnNode2) && find(fnNode1).equals(find(fnNode2))) {
					equalityPropagation(fnNode1, fnNode2);
				}
			}
		}
	}
	
	/**
	 * Join two @VPState. Two steps: 1) Create a new @VPState conjoinedState
	 * based on @param state1, add all the edge(equality relation) from @param
	 * state2 into @VPState conjoinedState. 2) Join the disEqualitySet.
	 * 
	 * @param state1
	 * @param other
	 * @return conjoinedState
	 */
	public VPState conjoin(VPState other) {

		if (this instanceof VPStateBottom || other instanceof VPStateBottom) {
			return mDomain.getmBottomState();
		}
		
		if (this instanceof VPStateTop) {
			return other;
		} else if (other instanceof VPStateTop) {
			return this;
		}
		
		VPState conjoinedState = this.copy();
		EqGraphNode thisGraphNode;
		EqGraphNode thisGraphNodeFind;
		boolean isContradic;

		for (VPDomainSymmetricPair<EqNode> otherPair : other.getDisEqualitySet()) {
			conjoinedState.getDisEqualitySet()
					.add(new VPDomainSymmetricPair<EqNode>(otherPair.getFirst(), otherPair.getSecond()));
		}

		for (final EqGraphNode otherGraphNode : other.getEqGraphNodeSet()) {
			if (!otherGraphNode.getRepresentative().equals(otherGraphNode.eqNode)) {
				thisGraphNode = conjoinedState.getEqNodeToEqGraphNodeMap().get(otherGraphNode.eqNode);
				thisGraphNodeFind = conjoinedState.getEqNodeToEqGraphNodeMap()
						.get(otherGraphNode.getRepresentative());
				isContradic = conjoinedState.addEquality(thisGraphNode.eqNode, thisGraphNodeFind.eqNode);
				if (isContradic) {
					return mDomain.getmBottomState();
				}
			}

		}

		return conjoinedState;
	}

	/**
	 * Disjoin two @VPState.
	 * 
	 * @param state1
	 * @param other
	 * @return disjoinedState
	 */
	public VPState disjoin(final VPState other) {

		if (this instanceof VPStateTop || other instanceof VPStateTop) {
			return mDomain.getmTopState();
		}
		
		if (this instanceof VPStateBottom) {
			return other;
		} else if (other instanceof VPStateBottom) {
			return this;
		}
		
		VPState disjoinedState = this.copy();
		EqNode node;
		EqGraphNode otherNode;

		boolean isContradic;

		disjoinedState.clearState();
		
		for (final VPDomainSymmetricPair<EqNode> otherPair : other.getDisEqualitySet()) {
			if (this.getDisEqualitySet().contains(otherPair)) {
				disjoinedState.getDisEqualitySet().add(new VPDomainSymmetricPair<EqNode>(otherPair.getFirst(), otherPair.getSecond()));
			}
		}

		for (final EqGraphNode thisNode : this.getEqGraphNodeSet()) {
			node = thisNode.eqNode;
			otherNode = other.getEqNodeToEqGraphNodeMap().get(node);

			EqNode thisNodeRepresentative = thisNode.getRepresentative();
			EqNode otherNodeRepresentative = otherNode.getRepresentative();
			
			if (thisNodeRepresentative.equals(otherNodeRepresentative)) {
				isContradic = disjoinedState.addEquality(node, thisNodeRepresentative);
				if (isContradic) {
					return mDomain.getmBottomState();
				}
			} else {
				
				if (other.find(node).equals(other.find(thisNodeRepresentative))) {
					isContradic = disjoinedState.addEquality(node, thisNodeRepresentative);
					if (isContradic) {
						return mDomain.getmBottomState();
					}
				} else if (this.find(node).equals(this.find(otherNodeRepresentative))) {
					isContradic = disjoinedState.addEquality(node, otherNodeRepresentative);
					if (isContradic) {
						return mDomain.getmBottomState();
					}
				}	
			}
		}

		return disjoinedState;
	}

	/**
	 * Three steps for adding equality relation into graph: 1) Union two nodes.
	 * 2) Propagate (merge congruence class). 3) Check for contradiction.
	 * 
	 * @param node1
	 * @param node2
	 * @return true if contradiction is met.
	 */
	public boolean addEquality(final EqNode node1, final EqNode node2) {
		// union(node1, node2);
		merge(node1, node2);
		return checkContradiction();
	}

	/**
	 * Three steps for adding disequality relation into graph: 1) Add relation
	 * to disEqualitySet. 2) Propagate (use ccchild). 3) Check for
	 * contradiction.
	 * 
	 * @param node1
	 * @param node2
	 * @return true if contradiction is met.
	 */
	public boolean addDisEquality(final EqNode node1, final EqNode node2) {

		addToDisEqSet(node1, node2);

		Set<EqNode> ccchild1 = ccchild(node1);
		Set<EqNode> ccchild2 = ccchild(node2);

		for (final EqNode child1 : ccchild1) {
			for (final EqNode child2 : ccchild2) {
				addDisEquality(child1, child2);
			}
		}

		return checkContradiction();
	}

	private void addToDisEqSet(final EqNode node1, final EqNode node2) {
		mDisEqualitySet.add(new VPDomainSymmetricPair<EqNode>(node1, node2));
	}

	public boolean checkContradiction() {

		for (final VPDomainSymmetricPair<EqNode> disEqPair : mDisEqualitySet) {
			if (find(disEqPair.getFirst()).equals(find(disEqPair.getSecond()))) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns the representative of a @param node's equivalence class.
	 * 
	 * @param node
	 * @return
	 */
	private EqNode find(final EqNode node) {
		if (this.mEqNodeToEqGraphNodeMap.get(node).getRepresentative().equals(node)) {
			return node;
		} else {
			return find(this.mEqNodeToEqGraphNodeMap.get(node).getRepresentative());
		}
	}

	/**
	 * Union of two equivalence classes.
	 * 
	 * @param node1
	 * @param node2
	 */
	private void union(final EqNode node1, final EqNode node2) {

		EqNode node1Find = find(node1);
		EqNode node2Find = find(node2);

		EqGraphNode graphNode1Find = this.mEqNodeToEqGraphNodeMap.get(node1Find);
		EqGraphNode graphNode2Find = this.mEqNodeToEqGraphNodeMap.get(node2Find);

		if (!graphNode1Find.eqNode.equals(graphNode2Find.eqNode)) {
			graphNode2Find.addToReverseRepresentative(node1Find);
			graphNode1Find.setRepresentative(graphNode2Find.eqNode);
			graphNode2Find.addToCcpar(graphNode1Find.getCcpar());
			graphNode2Find.addToCcchild(graphNode1Find.getCcchild());
		}
	}

	/**
	 * Returns the parents of all nodes in @param node's congruence class.
	 * 
	 * @param node
	 * @return
	 */
	private Set<EqNode> ccpar(final EqNode node) {
		return this.mEqNodeToEqGraphNodeMap.get(find(node)).getCcpar();
	}

	private Set<EqNode> ccchild(final EqNode node) {
		return this.mEqNodeToEqGraphNodeMap.get(find(node)).getCcchild();
	}

	/**
	 * Test whether @param node1 and @param node2 are congruent.
	 * 
	 * @param i1
	 * @param i2
	 * @return
	 */
	private boolean congruent(final EqNode node1, final EqNode node2) {
		if (!(node1 instanceof EqFunctionNode) || !(node2 instanceof EqFunctionNode)) {
			return false;
		}

		EqFunctionNode fnNode1 = (EqFunctionNode) node1;
		EqFunctionNode fnNode2 = (EqFunctionNode) node2;

		if (!(fnNode1.term.equals(fnNode2.term))) {
			return false;
		}
		if ((fnNode1.getArg() == null && fnNode2.getArg() != null)
				|| (fnNode2.getArg() == null && fnNode1.getArg() != null)) {
			return false;
		}
		if (!find(fnNode1.getArg()).equals(find(fnNode2.getArg()))) {
			return false;
		}
		return true;
	}

	/**
	 * Merge two congruence class. propagation.
	 * 
	 * @param i1
	 * @param i2
	 */
	private void merge(final EqNode node1, final EqNode node2) {
		if (!find(node1).equals(find(node2))) {
			union(node1, node2);
			equalityPropagation(node1, node2);
		}
	}
	
	private void equalityPropagation(final EqNode node1, final EqNode node2) {
		Set<EqNode> p1 = ccpar(node1);
		Set<EqNode> p2 = ccpar(node2);

		for (EqNode t1 : p1) {
			for (EqNode t2 : p2) {
				if (!(find(t1).equals(find(t2))) && congruent(t1, t2)) {
					merge(t1, t2);
				}
			}
		}
	}

	public void arrayAssignment(final Term firstArray, final Term secondArray) {

		havocArray(firstArray);

		for (final EqFunctionNode fnNode : mTermToFnNodeMap.get(secondArray)) {
			for (final EqNode eqNode : mEqNodeToEqGraphNodeMap.get(find(fnNode.arg)).getCcpar()) {
				if (eqNode instanceof EqFunctionNode) {
					if (((EqFunctionNode) eqNode).term.equals(firstArray)) {
						addEquality(eqNode, fnNode);
					}
				}
			}
		}
	}

	private boolean isArray(final TermVariable term) {
		return mTermToFnNodeMap.containsKey(term);
	}

	public void clearState() {
		this.getDisEqualitySet().clear();
		for (EqGraphNode graphNode : this.getEqGraphNodeSet()) {
			graphNode.setNodeToInitial();
		}
	}

	@Override
	public VPState addVariable(final IProgramVar variable) {
		if (mVars.contains(variable)) {
			return this;
		}
		final Set<IProgramVar> vars = AbsIntUtil.getFreshSet(mVars, mVars.size() + 1);
		vars.add(variable);
		return this;
	}

	@Override
	public VPState removeVariable(final IProgramVar variable) {
		if (!mVars.contains(variable)) {
			return this;
		}
		final Set<IProgramVar> vars = AbsIntUtil.getFreshSet(mVars);
		vars.remove(variable);
		return this;
	}

	@Override
	public VPState addVariables(final Collection<IProgramVar> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final Set<IProgramVar> vars = AbsIntUtil.getFreshSet(mVars, mVars.size() + variables.size());
		vars.addAll(variables);
		return this;
	}

	@Override
	public VPState removeVariables(final Collection<IProgramVar> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		return this;
	}

	public VPState copy() {

		final Map<Term, EqBaseNode> newTermToBaseNodeMap = new HashMap<Term, EqBaseNode>();
		for (final Entry<Term, EqBaseNode> entry : mTermToBaseNodeMap.entrySet()) {
			newTermToBaseNodeMap.put(entry.getKey(), entry.getValue());
		}

		final Map<Term, Set<EqFunctionNode>> newTermToFnNodeMap = new HashMap<Term, Set<EqFunctionNode>>();
		for (final Entry<Term, Set<EqFunctionNode>> entry : mTermToFnNodeMap.entrySet()) {
			Set<EqFunctionNode> fnNodeSet = new HashSet<EqFunctionNode>();
			for (EqFunctionNode fnNode : entry.getValue()) {
				fnNodeSet.add(fnNode);
			}
			newTermToFnNodeMap.put(entry.getKey(), fnNodeSet);
		}

		final Set<EqGraphNode> newEqGraphNodeSet = new HashSet<EqGraphNode>();
		final Map<EqNode, EqGraphNode> newEqNodeToEqGraphNodeMap = new HashMap<EqNode, EqGraphNode>();
		for (final Entry<EqNode, EqGraphNode> entry : mEqNodeToEqGraphNodeMap.entrySet()) {
			EqGraphNode graphNode = entry.getValue().copy();
			newEqGraphNodeSet.add(graphNode);
			newEqNodeToEqGraphNodeMap.put(entry.getKey(), graphNode);
		}
		
		final Set<VPDomainSymmetricPair<EqNode>> newDisEqualitySet = new HashSet<>();
		for (final VPDomainSymmetricPair<EqNode> pair : mDisEqualitySet) {
			newDisEqualitySet.add(new VPDomainSymmetricPair<EqNode>(pair.getFirst(), pair.getSecond()));
		}

		return new VPState(newEqGraphNodeSet, newTermToBaseNodeMap, newTermToFnNodeMap, newEqNodeToEqGraphNodeMap,
				newDisEqualitySet, mDomain);
	}

	@Override
	public boolean containsVariable(final IProgramVar var) {
		return mVars.contains(var);
	}

	@Override
	public Set<IProgramVar> getVariables() {
		return Collections.unmodifiableSet(mVars);
	}

	@Override
	public VPState patch(final VPState dominator) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean isEmpty() {
		return mVars.isEmpty();
	}

	@Override
	public boolean isBottom() {
		// A basic dataflow state is never bottom
		return false;
	}

	@Override
	public boolean isEqualTo(final VPState other) {
		if (other == null) {
			return false;
		}
		// TODO
		return false;
	}

	@Override
	public SubsetResult isSubsetOf(final VPState other) {
		if (isEqualTo(other)) {
			return SubsetResult.EQUAL;
		}
		return SubsetResult.NONE;
	}

	@Override
	public String toLogString() {

		final StringBuilder sb = new StringBuilder();

		sb.append("Graph: \n");
		for (EqGraphNode graphNode : mEqGraphNodeSet) {
			sb.append(graphNode.toString());
			sb.append('\n');
		}

		sb.append("Disequality Set:  \n");
		for (VPDomainSymmetricPair<EqNode> pair : mDisEqualitySet) {
			sb.append(pair.getFirst().toString());
			sb.append(", ");
			sb.append(pair.getSecond().toString());
			sb.append('\n');
		}

		System.out.println(sb.toString());

		return sb.toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final VPState other = (VPState) obj;
		if (!isEqualTo(other)) {
			return false;
		}
		// TODO
		return false;
	}

	@Override
	public Term getTerm(Script script) {
		// TODO: (alex:) do we want to describe the state precisely via a formula?? (useful for some assertion(s), and what else?..)
		return mDomain.getManagedScript().getScript().term("true");
	}

}
