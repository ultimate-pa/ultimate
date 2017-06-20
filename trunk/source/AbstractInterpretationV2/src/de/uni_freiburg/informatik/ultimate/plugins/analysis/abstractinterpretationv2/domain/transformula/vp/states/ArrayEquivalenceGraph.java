package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;

public class ArrayEquivalenceGraph<ACTION extends IIcfgTransition<IcfgLocation>,
	NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
	FUNCTION extends IEqFunctionIdentifier<FUNCTION>> {
	
	private final Set<VPDomainSymmetricPair<FUNCTION>> mFunctionDisequalities;
	
	/**
	 * constructs empty array equivalence graph
	 */
	public ArrayEquivalenceGraph() {
		// TODO Auto-generated constructor stub
		mFunctionDisequalities = new HashSet<>();
	}

	/**
	 * copy constructor
	 * @param original
	 */
	public ArrayEquivalenceGraph(ArrayEquivalenceGraph<ACTION, NODE, FUNCTION> original) {
//		for (FUNCTION rep : constraint.mFunctionEqualities.getAllRepresentatives()) {
//			mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(rep);
//			for (FUNCTION mem : constraint.mFunctionEqualities.getEquivalenceClassMembers(rep)) {
//				mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(mem);
//				mFunctionEqualities.union(mem, rep);
//			}
//		}

		mFunctionDisequalities = new HashSet<>(original.mFunctionDisequalities);
	}

//	public Collection<Set<FUNCTION>> getAllRepresentatives() {
	public Set<FUNCTION> getAllRepresentatives() {
		// TODO Auto-generated method stub
		return null;
	}

	public FUNCTION findAndConstructEquivalenceClassIfNeeded(FUNCTION rep) {
		// TODO Auto-generated method stub
		return null;
	}

	public Set<FUNCTION> getEquivalenceClassMembers(FUNCTION rep) {
		// TODO Auto-generated method stub
		return null;
	}

	public void union(FUNCTION mem, FUNCTION rep) {
		// TODO Auto-generated method stub
		
	}

	public Collection<Set<FUNCTION>> getAllEquivalenceClasses() {
		// TODO Auto-generated method stub
		return null;
	}

	public FUNCTION find(FUNCTION first) {
		// TODO Auto-generated method stub
		return null;
	}

	public boolean checkContradiction() {
		// TODO Auto-generated method stub
		return false;
	}

}
