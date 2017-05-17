package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class EqConstraint<
					ACTION extends IIcfgTransition<IcfgLocation>, 
					NODE extends IEqNodeIdentifier<FUNCTION>, 
					FUNCTION extends IEqFunctionIdentifier<FUNCTION>> 
	implements IAbstractState<EqConstraint<ACTION, NODE, FUNCTION>, IProgramVarOrConst>  {

	private boolean mIsFrozen = false;

	CongruenceGraph<NODE, FUNCTION> mElementCongruenceGraph;

	UnionFind<FUNCTION> mFunctionEqualities;
	
	Set<VPDomainSymmetricPair<FUNCTION>> mFunctionDisequalities;

	public void merge(NODE node1, NODE node2) {
		mElementCongruenceGraph.merge(node1, node2);
	}

	
	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
		mElementCongruenceGraph.freeze();
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
		return mElementCongruenceGraph.getDisequalities();
	}


	/**
	 * "Raw" means here that the disequality is not yet normalized so as to speak about equivalence representatives.
	 * 
	 * @param first
	 * @param second
	 */
	public void addRawDisequality(NODE first, NODE second) {
		assert !mIsFrozen;
		mElementCongruenceGraph.addDisequality(mElementCongruenceGraph.find(first), mElementCongruenceGraph.find(second));
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
		if (mElementCongruenceGraph.checkContradiction()) {
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

	/*
	 * **************** methods inherited from IAbstractState ****************
	 */



	@Override
	public EqConstraint<ACTION, NODE, FUNCTION> addVariable(IProgramVarOrConst variable) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public EqConstraint<ACTION, NODE, FUNCTION> removeVariable(IProgramVarOrConst variable) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public EqConstraint<ACTION, NODE, FUNCTION> addVariables(Collection<IProgramVarOrConst> variables) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public EqConstraint<ACTION, NODE, FUNCTION> removeVariables(Collection<IProgramVarOrConst> variables) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public boolean containsVariable(IProgramVarOrConst var) {
		// TODO Auto-generated method stub
		return false;
	}


	@Override
	public Set<IProgramVarOrConst> getVariables() {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public EqConstraint<ACTION, NODE, FUNCTION> patch(EqConstraint<ACTION, NODE, FUNCTION> dominator) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public EqConstraint<ACTION, NODE, FUNCTION> intersect(EqConstraint<ACTION, NODE, FUNCTION> other) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public EqConstraint<ACTION, NODE, FUNCTION> union(EqConstraint<ACTION, NODE, FUNCTION> other) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public boolean isEmpty() {
		// TODO Auto-generated method stub
		return false;
	}


	@Override
	public boolean isEqualTo(EqConstraint<ACTION, NODE, FUNCTION> other) {
		// TODO Auto-generated method stub
		return false;
	}


	@Override
	public SubsetResult isSubsetOf(
			EqConstraint<ACTION, NODE, FUNCTION> other) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public EqConstraint<ACTION, NODE, FUNCTION> compact() {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public Term getTerm(Script script) {
		// TODO Auto-generated method stub
		return null;
	}


	@Override
	public String toLogString() {
		// TODO Auto-generated method stub
		return null;
	}


	public void renameVariables(Map<Term, Term> substitutionMapping) {
		assert !mIsFrozen;
		
		mElementCongruenceGraph.renameVariables(substitutionMapping);
		
		final UnionFind<FUNCTION> newFunctionUF = new UnionFind<>();
		for (Entry<FUNCTION, FUNCTION> fEq : getSupportingFunctionEqualities()) {
			FUNCTION renamedF1 = newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
					fEq.getKey().renameVariables(substitutionMapping));
			FUNCTION renamedF2 = newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
					fEq.getKey().renameVariables(substitutionMapping));
			newFunctionUF.union(renamedF1, renamedF2);
		}
		mFunctionEqualities = newFunctionUF;
	}

}
