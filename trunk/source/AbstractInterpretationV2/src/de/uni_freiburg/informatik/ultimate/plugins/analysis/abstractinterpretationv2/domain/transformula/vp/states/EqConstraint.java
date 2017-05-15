package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class EqConstraint<NODE extends IEqNodeIdentifier<FUNCTION>, FUNCTION>  {

	private boolean mIsFrozen = false;

	CongruenceGraph<NODE, FUNCTION> mElementEqualityGraph;

//	Set<VPDomainSymmetricPair<NODE>> mElementDisequalities;
	
	UnionFind<FUNCTION> mFunctionEqualities;
	
	Set<VPDomainSymmetricPair<FUNCTION>> mFunctionDisequalities;

	public void merge(NODE node1, NODE node2) {
		mElementEqualityGraph.merge(node1, node2);
	}

	
	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
		mElementEqualityGraph.freeze();
		mFunctionDisequalities = Collections.unmodifiableSet(mFunctionDisequalities);
	}


	public boolean isBottom() {
		// TODO Auto-generated method stub
		return false;
	}


	public Set<NODE> getAllNodes() {
		// TODO Auto-generated method stub
		return null;
	}


	public void addNodes(Set<EqNode> allNodes) {
		// TODO Auto-generated method stub
		
	}


	public HashRelation<NODE, NODE> getSupportingElementEqualities() {
		// TODO Auto-generated method stub
		return null;
	}


	public Set<VPDomainSymmetricPair<NODE>> getElementDisequalities() {
		return mElementEqualityGraph.getDisequalities();
	}


	/**
	 * "Raw" means here that the disequality is not yet normalized so as to speak about equivalence representatives.
	 * 
	 * @param first
	 * @param second
	 */
	public void addRawDisequality(NODE first, NODE second) {
		assert !mIsFrozen;
		mElementEqualityGraph.addDisequality(mElementEqualityGraph.find(first), mElementEqualityGraph.find(second));
	}


	public HashRelation<FUNCTION, FUNCTION> getSupportingFunctionEqualities() {
		/*
		 * plan: for each equivalence class, iterate over the elements and report an equality for each two consecutive
		 *  elements
		 */
		HashRelation<FUNCTION, FUNCTION> result = new HashRelation<>();
		for (Set<FUNCTION> eqClass : mFunctionEqualities.getAllEquivalenceClasses()) {
			FUNCTION lastElement;
			FUNCTION currentElement = null;
			for (FUNCTION el : eqClass) {
				lastElement = currentElement;
				currentElement = el;
				if (lastElement != null) {
					result.addPair(lastElement, currentElement);
				}
			}
		}
		
		return result;
	}


	public void addFunctionEquality(FUNCTION key, FUNCTION value) {
		mFunctionEqualities.union(mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(key),
				mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(value));
	}


	public  Set<VPDomainSymmetricPair<FUNCTION>> getFunctionDisequalites() {
		return mFunctionDisequalities;
	}


	public void addFunctionDisequality(FUNCTION first, FUNCTION second) {
		mFunctionDisequalities.add(new VPDomainSymmetricPair<FUNCTION>(first, second));
	}


	public boolean checkForContradiction() {
		if (mElementEqualityGraph.checkContradiction()) {
			return true;
		}
		for (VPDomainSymmetricPair<FUNCTION> fDeq : mFunctionDisequalities) {
			if (mFunctionEqualities.find(fDeq.getFirst()).equals(mFunctionEqualities.find(fDeq.getSecond()))) {
				return true;
			}
		}
		return false;
	}


	public boolean isFrozen() {
		return mIsFrozen;
	}


	public void projectExistentially(Set<TermVariable> varsToProjectAway) {
		// TODO Auto-generated method stub
		
	}


	public void renameVariables(Map<Term, Term> substitutionMapping) {
		// TODO Auto-generated method stub
		
	}
}
