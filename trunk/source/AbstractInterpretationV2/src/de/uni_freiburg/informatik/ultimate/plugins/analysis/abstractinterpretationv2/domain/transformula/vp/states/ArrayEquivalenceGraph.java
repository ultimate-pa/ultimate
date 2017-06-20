package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

public class ArrayEquivalenceGraph<ACTION extends IIcfgTransition<IcfgLocation>,
	NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
	FUNCTION extends IEqFunctionIdentifier<FUNCTION>> {
	
	private UnionFind<FUNCTION> mFunctionEqualities;
	private Set<VPDomainSymmetricPair<FUNCTION>> mFunctionDisequalities;
	private boolean mIsFrozen = false;
	
	/**
	 * constructs empty array equivalence graph
	 */
	public ArrayEquivalenceGraph() {
		mFunctionEqualities = new UnionFind<>();
		mFunctionDisequalities = new HashSet<>();
	}

	/**
	 * copy constructor
	 * @param original
	 */
	public ArrayEquivalenceGraph(ArrayEquivalenceGraph<ACTION, NODE, FUNCTION> original) {
		mFunctionEqualities = new UnionFind<>();
		for (FUNCTION rep : original.mFunctionEqualities.getAllRepresentatives()) {
			mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(rep);
			for (FUNCTION mem : original.mFunctionEqualities.getEquivalenceClassMembers(rep)) {
				mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(mem);
				mFunctionEqualities.union(mem, rep);
			}
		}

		mFunctionDisequalities = new HashSet<>(original.mFunctionDisequalities);
	}

	public void union(FUNCTION func1, FUNCTION func2) {
		assert !mIsFrozen;

		mFunctionEqualities.union(mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(func1),
				mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(func2));
		
	}

	public void addFunctionDisequality(FUNCTION first, FUNCTION second) {
		assert !mIsFrozen;
		
		final FUNCTION firstRep = mFunctionEqualities.find(first);
		final FUNCTION secondRep = mFunctionEqualities.find(second);

		mFunctionDisequalities.add(new VPDomainSymmetricPair<FUNCTION>(firstRep, secondRep));
	}

	public void renameVariables(Map<Term, Term> substitutionMapping) {
		assert !mIsFrozen;

		final UnionFind<FUNCTION> newFunctionUF = new UnionFind<>();
		for (Set<FUNCTION> eqc : mFunctionEqualities.getAllEquivalenceClasses()) {
			FUNCTION first = newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
					eqc.iterator().next().renameVariables(substitutionMapping));
			for (FUNCTION f : eqc) {
				FUNCTION renamedF = newFunctionUF.findAndConstructEquivalenceClassIfNeeded(
						f.renameVariables(substitutionMapping));
				newFunctionUF.union(first, renamedF);
			}
		}
		mFunctionEqualities = newFunctionUF;	
		
		
		final Set<VPDomainSymmetricPair<FUNCTION>> newFunctionDisequalites = new HashSet<>();
		for (VPDomainSymmetricPair<FUNCTION> fDeq : mFunctionDisequalities) {
			newFunctionDisequalites.add(new VPDomainSymmetricPair<FUNCTION>(
					fDeq.getFirst().renameVariables(substitutionMapping), 
					fDeq.getSecond().renameVariables(substitutionMapping)));
		}
		mFunctionDisequalities = newFunctionDisequalites;
	}

	public void havocFunction(FUNCTION func) {
		assert !mIsFrozen;
		// remove from function disequalities
		mFunctionDisequalities.removeIf(pair -> pair.contains(func));
	
		// remove from function equalities
		final UnionFind<FUNCTION> newFunctionEqualities = new UnionFind<>();
		// (union find has no remove -> has to be built anew)
		for (Set<FUNCTION> eqc : mFunctionEqualities.getAllEquivalenceClasses()) {
			// look for an element that is not func --> everything but func will be merged with it
			final Iterator<FUNCTION> eqcIt = eqc.iterator();
			FUNCTION first = eqcIt.next();
			while (first.dependsOn(func)) {
				if (eqcIt.hasNext()) {
					first = eqcIt.next();
				} else {
					// equivalence class has only elements that need to be havocced
					for (FUNCTION el : eqc) {
						newFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(el);
					}
					continue;
				}
			}
			assert !first.dependsOn(func);

			// construct the new equivalence class by merging all elements of the old, except func
			for (FUNCTION el : eqc) {
				newFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(el);
				if (el.dependsOn(func)) {
					// el is havocced --> don't merge its equivalence class
					continue;
				}
				newFunctionEqualities.union(first, el);
			}
		}
		mFunctionEqualities = newFunctionEqualities;	
	}

	public void addFunction(FUNCTION func) {
		assert !mIsFrozen;
		mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(func);
	}

	public void freeze() {
		assert !mIsFrozen;
		mIsFrozen = true;
	}

	public Set<FUNCTION> getEquivalenceClassMembers(FUNCTION rep) {
		return mFunctionEqualities.getEquivalenceClassMembers(rep);
	}

	public Collection<FUNCTION> getAllRepresentatives() {
		return mFunctionEqualities.getAllRepresentatives();
	}

	public Collection<Set<FUNCTION>> getAllEquivalenceClasses() {
		return mFunctionEqualities.getAllEquivalenceClasses();
	}

	public boolean checkContradiction() {
		for (VPDomainSymmetricPair<FUNCTION> fDeq : mFunctionDisequalities) {
			if (mFunctionEqualities.find(fDeq.getFirst()).equals(mFunctionEqualities.find(fDeq.getSecond()))) {
				return true;
			}
		}
		return false;
	}

	public Set<VPDomainSymmetricPair<FUNCTION>> getFunctionDisequalities() {
		return mFunctionDisequalities;
	}

	public boolean areEqual(FUNCTION func1, FUNCTION func2) {
		final FUNCTION func1rep = mFunctionEqualities.find(func1);
		final FUNCTION func2rep = mFunctionEqualities.find(func2);
		if (func1rep == null || func2rep == null) {
			return false;
		}
		return func1rep.equals(func2rep);
	}

	public boolean areUnequal(FUNCTION func1, FUNCTION func2) {
		final FUNCTION rep1 = mFunctionEqualities.find(func1);
		final FUNCTION rep2 = mFunctionEqualities.find(func2);
		if (rep1 == null || rep2 == null) {
			return false;
		}
		return mFunctionDisequalities.contains(new VPDomainSymmetricPair<FUNCTION>(rep1, rep2));
	}

}
