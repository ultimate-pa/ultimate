/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.util.AbsIntUtil;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPState implements IAbstractState<VPState, CodeBlock, IProgramVar> {

	private static final String TERM_FUNC_NAME_AND = "and";
	private static final String TERM_TRUE = "true";
	private static final String TERM_FUNC_NAME_DISTINCT = "distinct";

	private final Set<IProgramVar> mVars;

	final Collection<EqGraphNode> mEqGraphNodeSet;
	private final Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;

	private Set<VPDomainSymmetricPair<EqGraphNode>> mDisEqualitySet;

	private final VPDomain mDomain;
	private final Script mScript;

	VPState(VPDomain domain) {
		this(Collections.emptyMap(), Collections.emptySet(), domain);
	}

	VPState(Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap, Set<VPDomainSymmetricPair<EqGraphNode>> disEqualitySet,
			VPDomain domain) {
		mVars = new HashSet<>();
		mEqNodeToEqGraphNodeMap = eqNodeToEqGraphNodeMap;
		mEqGraphNodeSet = mEqNodeToEqGraphNodeMap.values();
		mDisEqualitySet = disEqualitySet;
		mDomain = domain;
		mScript = mDomain.getManagedScript().getScript();
	}

	public Set<VPDomainSymmetricPair<EqGraphNode>> getDisEqualitySet() {
		return mDisEqualitySet;
	}

	public void setDisEqualitySet(Set<VPDomainSymmetricPair<EqGraphNode>> disEqualitySet) {
		this.mDisEqualitySet = disEqualitySet;
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		return mEqNodeToEqGraphNodeMap;
	}

	void restorePropagation(final EqFunctionNode node) {

		final Set<EqFunctionNode> fnNodeSet = mDomain.getArrayIdToEqFnNodeMap().getImage(node.getFunction());
		for (final EqFunctionNode fnNode1 : fnNodeSet) {
			for (final EqFunctionNode fnNode2 : fnNodeSet) {
				if (!fnNode1.equals(fnNode2) && find(this.getEqNodeToEqGraphNodeMap().get(fnNode1))
						.equals(find(this.getEqNodeToEqGraphNodeMap().get(fnNode2)))) {
					equalityPropagation(this.getEqNodeToEqGraphNodeMap().get(fnNode1),
							this.getEqNodeToEqGraphNodeMap().get(fnNode2));
				}
			}
		}
	}

	public void addToDisEqSet(final EqGraphNode node1, final EqGraphNode node2) {
		this.getDisEqualitySet().add(new VPDomainSymmetricPair<EqGraphNode>(node1, node2));
	}

	/**
	 * Use disEqualitySet to check if there exist contradiction in the graph.
	 * 
	 * @return true if there is contradiction
	 */
	boolean checkContradiction() {

		for (final VPDomainSymmetricPair<EqGraphNode> disEqPair : this.getDisEqualitySet()) {
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
	public EqGraphNode find(final EqGraphNode node) {
		if (node.getRepresentative().equals(node)) {
			return node;
		} else {
			return find(node.getRepresentative());
		}
	}

	/**
	 * Returns the parents of all nodes in @param node's congruence class.
	 * 
	 * @param node
	 * @return
	 */
	private Set<EqGraphNode> ccpar(final EqGraphNode node) {
		return find(node).getCcpar();
	}

	public HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild(final EqGraphNode node) {
		return find(node).getCcchild();
	}

	/**
	 * Check whether @param node1 and @param node2 are congruent.
	 * 
	 * @param node1
	 * @param node2
	 * @return true if they are congruent
	 */
	private boolean congruent(final EqGraphNode node1, final EqGraphNode node2) {
		if (!(node1.eqNode instanceof EqFunctionNode) || !(node2.eqNode instanceof EqFunctionNode)) {
			return false;
		}

		EqFunctionNode fnNode1 = (EqFunctionNode) node1.eqNode;
		EqFunctionNode fnNode2 = (EqFunctionNode) node2.eqNode;

		if (!(fnNode1.getFunction().equals(fnNode2.getFunction()))) {
			return false;
		}
		return congruentIgnoreFunctionSymbol(fnNode1, fnNode2);
	}

	/**
	 * Checks if the arguments of the given EqFunctionNodes are all congruent.
	 * 
	 * @param fnNode1
	 * @param fnNode2
	 * @return
	 */
	boolean congruentIgnoreFunctionSymbol(final EqFunctionNode fnNode1, final EqFunctionNode fnNode2) {
		assert fnNode1.getArgs() != null && fnNode2.getArgs() != null;
		assert fnNode1.getArgs().size() == fnNode2.getArgs().size();

		for (int i = 0; i < fnNode1.getArgs().size(); i++) {
			EqNode fnNode1Arg = fnNode1.getArgs().get(i);
			EqNode fnNode2Arg = fnNode2.getArgs().get(i);
			if (!find(this.getEqNodeToEqGraphNodeMap().get(fnNode1Arg))
					.equals(find(this.getEqNodeToEqGraphNodeMap().get(fnNode2Arg)))) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Merge two congruence class. propagation.
	 * 
	 * @param i1
	 * @param i2
	 */
	void merge(final EqGraphNode node1, final EqGraphNode node2) {
		if (!find(node1).equals(find(node2))) {
			union(node1, node2);
			equalityPropagation(node1, node2);
		}
	}

	/**
	 * Union of two equivalence classes.
	 * 
	 * @param node1
	 * @param node2
	 */
	private void union(final EqGraphNode node1, final EqGraphNode node2) {

		EqGraphNode graphNode1Find = find(node1);
		EqGraphNode graphNode2Find = find(node2);

		if (!graphNode1Find.equals(graphNode2Find)) {
			graphNode2Find.addToReverseRepresentative(graphNode1Find);
			graphNode1Find.setRepresentative(graphNode2Find);
			graphNode2Find.addToCcpar(graphNode1Find.getCcpar());
			for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode1Find.getCcchild().entrySet()) {
				graphNode2Find.getCcchild().addPair(entry.getKey(), entry.getValue());
			}
//			graphNode2Find.addToCcchild(graphNode1Find.getCcchild());
		}
	}

	private void equalityPropagation(final EqGraphNode node1, final EqGraphNode node2) {
		Set<EqGraphNode> p1 = ccpar(node1);
		Set<EqGraphNode> p2 = ccpar(node2);

		for (EqGraphNode t1 : p1) {
			for (EqGraphNode t2 : p2) {
				if (!(find(t1).equals(find(t2))) && congruent(t1, t2)) {
					merge(t1, t2);
				}
			}
		}
	}



//	private boolean isArray(final TermVariable term) {
//		return mDomain.getArrayIdToEqFnNodeMap().containsKey(term);
//	}

	/**
	 * Erase all the edges in the graph of this state.
	 */
	public void clearState() {
		this.getDisEqualitySet().clear();
		for (EqGraphNode graphNode : this.mEqGraphNodeSet) {
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

	/**
	 * 
	 * @return a fresh @VPState that have the same equality/disequality edges
	 *         with the calling state.
	 */
	@Deprecated
	public VPState copy() {

		final Map<EqNode, EqGraphNode> newEqNodeToEqGraphNodeMap = new HashMap<>();
		for (final Entry<EqNode, EqGraphNode> entry : this.getEqNodeToEqGraphNodeMap().entrySet()) {
			EqGraphNode graphNode = entry.getValue().copy();
			newEqNodeToEqGraphNodeMap.put(entry.getKey(), graphNode);
		}

		final Set<VPDomainSymmetricPair<EqGraphNode>> newDisEqualitySet = new HashSet<>();
		for (final VPDomainSymmetricPair<EqGraphNode> pair : this.getDisEqualitySet()) {
			newDisEqualitySet
					.add(new VPDomainSymmetricPair<EqGraphNode>(newEqNodeToEqGraphNodeMap.get(pair.getFirst().eqNode),
							newEqNodeToEqGraphNodeMap.get(pair.getSecond().eqNode)));
		}

		return new VPState(newEqNodeToEqGraphNodeMap, newDisEqualitySet, mDomain);
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
		return false;
	}

	@Override
	public boolean isEqualTo(final VPState other) {

		Script script = mDomain.getManagedScript().getScript();
		
		TermVarsProc tvpThis = TermVarsProc.computeTermVarsProc(this.getTerm(mScript), mScript, mDomain.getBoogie2Smt().getBoogie2SmtSymbolTable());
		TermVarsProc tvpOther = TermVarsProc.computeTermVarsProc(other.getTerm(mScript), mScript, mDomain.getBoogie2Smt().getBoogie2SmtSymbolTable());
		
		/*
		 * build a term that says
		 *  (not (this.getTerm() <--> other.getTerm))
		 */
		Term equiv = script.term(
				TERM_FUNC_NAME_DISTINCT, 
				new Term[] { tvpThis.getClosedFormula(), tvpOther.getClosedFormula() });
	

		script.echo(new QuotedObject("VPState.isEqualTo()"));
		script.push(1);
		script.assertTerm(equiv);
		LBool res = script.checkSat();
		script.pop(1);

		return res == LBool.UNSAT;

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
            if (graphNode.getRepresentative() == graphNode) {
                // print only the interesting graph nodes in full
                sb.append(graphNode.eqNode.toString());
            } else {
                sb.append(graphNode.toString());
			sb.append('\n');
            }
		}

		sb.append("Disequality Set:  \n");
		for (VPDomainSymmetricPair<EqGraphNode> pair : mDisEqualitySet) {
			sb.append(pair.getFirst().toString());
			sb.append(", ");
			sb.append(pair.getSecond().toString());
			sb.append('\n');
		}

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
		if (isEqualTo(other)) {
			return true;
		}
		return false;
	}

	@Override
	public Term getTerm(Script script) {

		Term trueTerm = mDomain.getManagedScript().getScript().term(TERM_TRUE);

		Term disEqualityFirst;
		Term disEqualitySecond;
		Set<Term> distinctTermSet = new HashSet<>();
		Term disEquality;

		for (VPDomainSymmetricPair<EqGraphNode> pair : this.mDisEqualitySet) {
			disEqualityFirst = pair.getFirst().eqNode.getTerm(mScript);
			disEqualitySecond = pair.getSecond().eqNode.getTerm(mScript);
			distinctTermSet.add(mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_DISTINCT, disEqualityFirst,
					disEqualitySecond));
		}

		if (distinctTermSet.isEmpty()) {
			disEquality = trueTerm;
		} else if (distinctTermSet.size() == 1) {
			disEquality = mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND,
					distinctTermSet.iterator().next(), trueTerm);
		} else {
			disEquality = mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND,
					distinctTermSet.toArray(new Term[distinctTermSet.size()]));
		}

		Term equalityFirst;
		Term equalitySecond;
		Set<Term> equalityTermSet = new HashSet<>();
		Term equality;

		for (EqGraphNode graphNode : this.mEqGraphNodeSet) {
			if (!graphNode.equals(graphNode.getRepresentative())) {
				equalityFirst = graphNode.eqNode.getTerm(mScript);
				equalitySecond = graphNode.getRepresentative().eqNode.getTerm(mScript);
				equalityTermSet.add(mDomain.getManagedScript().getScript().term("=", equalityFirst, equalitySecond));
			}
		}

		if (equalityTermSet.isEmpty()) {
			equality = trueTerm;
		} else if (equalityTermSet.size() == 1) {
			equality = mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND,
					equalityTermSet.iterator().next(), trueTerm);
		} else {
			equality = mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND,
					equalityTermSet.toArray(new Term[equalityTermSet.size()]));
		}

		return mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND, disEquality, equality);
	}

	public Set<EqNode> getEquivalenceRepresentatives() {
		Set<EqNode> result = new HashSet<>();
		for (EqGraphNode egn : mEqGraphNodeSet) {
			if (egn.getRepresentative() == egn) {
				result.add(egn.eqNode);
			}
		}
		return result;
	}

	/**
	 * 
	 * @param node
	 * @return All the eqNodes that are in the same equivalence class as node in
	 *         this state.
	 */
	public Set<EqNode> getEquivalentEqNodes(EqNode node) {
		Set<EqNode> result = new HashSet<>();
		for (EqGraphNode egn : mEqGraphNodeSet) {
			if (find(egn).eqNode == node) {
				result.add(egn.eqNode);
			}
		}
		return result;
	}

	public VPDomain getDomain() {
		return mDomain;
	}
}
