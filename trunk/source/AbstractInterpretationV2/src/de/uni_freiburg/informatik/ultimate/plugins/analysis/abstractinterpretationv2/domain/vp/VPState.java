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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
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
	
	private Map<Term, Set<Term>> mEqualityMap;
	private Map<Term, Set<Term>> mDisEqualityMap;
	
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

	public Map<Term, Set<Term>> getmEqualityMap() {
		return mEqualityMap;
	}

	public void setmEqualityMap(Map<Term, Set<Term>> mEqualityMap) {
		this.mEqualityMap = mEqualityMap;
	}

	public Map<Term, Set<Term>> getmDisEqualityMap() {
		return mDisEqualityMap;
	}

	public void setmDisEqualityMap(Map<Term, Set<Term>> mDisEqualityMap) {
		this.mDisEqualityMap = mDisEqualityMap;
	}

	VPState(Set<EqGraphNode> eqGraphNodeSet, 
			Map<Term, EqBaseNode> termToBaseNodeMap,
			Map<Term, Set<EqFunctionNode>> termToFnNodeMap,
			Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap,
			Map<Term, Set<Term>> equalityMap, 
			Map<Term, Set<Term>> disEqualityMap) {
		mVars = new HashSet<IProgramVar>();
		mEqGraphNodeSet = eqGraphNodeSet;
		mTermToBaseNodeMap = termToBaseNodeMap;
		mTermToFnNodeMap = termToFnNodeMap;
		mEqNodeToEqGraphNodeMap = eqNodeToEqGraphNodeMap;
		mEqualityMap = equalityMap;
		mDisEqualityMap = disEqualityMap;
	}
	
	private VPState conjoin(VPState state1, VPState state2) {
		
		VPState conjoinedState = state1.copy();
		
		return null;
		
	}

	private VPState disjoin(VPState state1, VPState state2) {
		return null;
	}
	
	private void addEquality(Term term1, Term term2) {
		
	}
	
	private void addDisEquality(Term term1, Term term2) {
		
	}
	
	/**
	 * Returns the representative of a @param node's equivalence class.
	 * 
	 * @param node
	 * @return
	 */
	private EqGraphNode find(EqGraphNode node) {
		if (node.getFind() == node.getEqNode()) {
			return node;
		} else {
			return find(node);
		}
	}
	
	/**
	 * Union of two equivalence classes.
	 * 
	 * @param node1
	 * @param node2
	 */
	private void union(EqGraphNode node1, EqGraphNode node2) {

		EqGraphNode findNode1 = find(node1);
		EqGraphNode findNode2 = find(node2);
		
		findNode1.setFind(findNode2.eqNode);
		findNode2.ccpar.addAll(findNode1.ccpar);
		findNode1.ccpar.clear();
	}
	
	/**
	 * Returns the parents of all nodes in @param node's congruence class.
	 * 
	 * @param node
	 * @return
	 */
	private Set<EqNode> ccpar(EqGraphNode node) {
		return find(node).ccpar;
	}
	
	/**
	 * Test whether @param i1 and @param i2 are congruent.
	 * 
	 * @param i1
	 * @param i2
	 * @return
	 */
	private boolean congruent(EqGraphNode node1, EqGraphNode node2) {
		if (!(node1.eqNode instanceof EqFunctionNode) || !(node2.eqNode instanceof EqFunctionNode)) {
			return false;
		}
		
		EqFunctionNode fnNode1 = (EqFunctionNode)node1.eqNode;
		EqFunctionNode fnNode2 = (EqFunctionNode)node2.eqNode;
		
		if (!(fnNode1.term.equals(fnNode2.term))) {
			return false;
		}
		if ((fnNode1.getArg() == null && fnNode2.getArg() != null)
				|| (fnNode2.getArg() == null && fnNode1.getArg() != null)) {
			return false;
		}
		if (fnNode1.getArg() != fnNode2.getArg()) {
			return false;
		}
		return true;
	}
	
	/**
	 * Merge two congruence class.
	 * 
	 * @param i1
	 * @param i2
	 */
	private void merge(EqGraphNode i1, EqGraphNode i2) {
		
		if (find(i1) != find(i2)) {
			
			Set<EqNode> p1 = ccpar(i1);
			Set<EqNode> p2 = ccpar(i2);
			
			union(i1, i2);
			
			for (EqNode t1 : p1) {
				for (EqNode t2 : p2) {
					if ((find(mEqNodeToEqGraphNodeMap.get(t1)) != find(mEqNodeToEqGraphNodeMap.get(t2)))
							&& congruent(mEqNodeToEqGraphNodeMap.get(t1), mEqNodeToEqGraphNodeMap.get(t2))) {
						merge(mEqNodeToEqGraphNodeMap.get(t1), mEqNodeToEqGraphNodeMap.get(t2));
					}
				}
			}
			
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
		
		final Set<EqGraphNode> newEqGraphNodeSet = new HashSet<EqGraphNode>();
		for (EqGraphNode node : mEqGraphNodeSet) {
			newEqGraphNodeSet.add(node.copy());
			
		}
		
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
		
		final Map<EqNode, EqGraphNode> newEqNodeToEqGraphNodeMap = new HashMap<EqNode, EqGraphNode>();
		for (final Entry<EqNode, EqGraphNode> entry : mEqNodeToEqGraphNodeMap.entrySet()) {
			newEqNodeToEqGraphNodeMap.put(entry.getKey(), entry.getValue().copy());
		}
		
		final Map<Term, Set<Term>> newEqualityMap = new HashMap<Term, Set<Term>>();
		for (final Entry<Term, Set<Term>> entry : mEqualityMap.entrySet()) {
			final Set<Term> newEqTermSet = new HashSet<Term>();
			newEqTermSet.addAll(entry.getValue());
			newEqualityMap.put(entry.getKey(), newEqTermSet);
		}
		
		final Map<Term, Set<Term>> newDisEqualityMap = new HashMap<Term, Set<Term>>();
		for (final Entry<Term, Set<Term>> entry : mDisEqualityMap.entrySet()) {
			final Set<Term> newDisEqTermSet = new HashSet<Term>();
			newDisEqTermSet.addAll(entry.getValue());
			newDisEqualityMap.put(entry.getKey(), newDisEqTermSet);
		}
		
		return new VPState(newEqGraphNodeSet, newTermToBaseNodeMap, newTermToFnNodeMap, newEqNodeToEqGraphNodeMap, newEqualityMap, newDisEqualityMap);		
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
	public Term getTerm(final Script script, final Boogie2SMT bpl2smt) {
		return script.term("true");
	}

	@Override
	public String toLogString() {
		final StringBuilder sb = new StringBuilder();
		sb.append('{');	
		sb.append("->");
		sb.append('}');
		
		// TODO
		
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

	VPState union(final VPState other) {
		if (other == null || other == this || other.isEqualTo(this)) {
			return this;
		}

		// TODO

		return null;
//		return new VPState(vars, def, use, reachdef, noWrite, mEqNodeSet);
	}

}
