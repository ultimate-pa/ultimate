/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.IEqNodeIdentifier;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.IEqFunctionIdentifier;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <ACTION>
 * @param <NODE>
 * @param <FUNCTION>
 */
public class ArrayEquivalenceGraph<ACTION extends IIcfgTransition<IcfgLocation>,
	NODE extends IEqNodeIdentifier<NODE, FUNCTION>, 
	FUNCTION extends IEqFunctionIdentifier<NODE, FUNCTION>> {
	
	private UnionFind<FUNCTION> mFunctionEqualities;
	
	/**
	 * stores all disequalities in terms of equivalence representatives
	 */
	private Set<VPDomainSymmetricPair<FUNCTION>> mFunctionDisequalities;
	private boolean mIsFrozen = false;

	private final EqConstraint<ACTION, NODE, FUNCTION> mOwner;
	
	/**
	 * constructs empty array equivalence graph
	 */
	public ArrayEquivalenceGraph(EqConstraint<ACTION, NODE, FUNCTION> owner) {
		mFunctionEqualities = new UnionFind<>();
		mFunctionDisequalities = new HashSet<>();
		mOwner = owner;
	}

	/**
	 * copy constructor
	 * @param original
	 */
	public ArrayEquivalenceGraph(ArrayEquivalenceGraph<ACTION, NODE, FUNCTION> original,
			EqConstraint<ACTION, NODE, FUNCTION> owner) {
		mOwner = owner;
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

		FUNCTION func1Rep = mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(func1);
		FUNCTION func2Rep = mFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(func2);
		mFunctionEqualities.union(func1Rep, func2Rep);
		
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

	public void havocFunction(FUNCTION funcToBeHavocced) {
		assert !mIsFrozen;
		// remove from function disequalities
		mFunctionDisequalities.removeIf(pair -> pair.contains(mFunctionEqualities.find(funcToBeHavocced)));
	
		// remove from function equalities
		mFunctionEqualities.remove(funcToBeHavocced);
//		final UnionFind<FUNCTION> newFunctionEqualities = new UnionFind<>();
//		// (union find has no remove -> has to be built anew)
//		for (Set<FUNCTION> eqc : mFunctionEqualities.getAllEquivalenceClasses()) {
//			// look for an element that is not func --> everything but func will be merged with it
//			final Iterator<FUNCTION> eqcIt = eqc.iterator();
//			FUNCTION first = eqcIt.next();
////			while (first.dependsOn(funcToBeHavocced)) {
//			while (first.equals(funcToBeHavocced)) {
//				if (eqcIt.hasNext()) {
//					first = eqcIt.next();
//				} else {
//					// equivalence class has only elements that need to be havocced
//					for (FUNCTION el : eqc) {
//						newFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(el);
//					}
//					continue;
//				}
//			}
////			assert !first.dependsOn(funcToBeHavocced);
//			assert !first.equals(funcToBeHavocced);
//
//			// construct the new equivalence class by merging all elements of the old, except func
//			for (FUNCTION el : eqc) {
////				if (el.dependsOn(funcToBeHavocced)) {
//				if (el.equals(funcToBeHavocced)) {
//					// el is havocced --> don't merge its equivalence class
//					continue;
//				}
//				newFunctionEqualities.findAndConstructEquivalenceClassIfNeeded(el);
//				newFunctionEqualities.union(first, el);
//			}
//		}
//		mFunctionEqualities = newFunctionEqualities;	
		
		assert mFunctionEqualities.getAllEquivalenceClasses().isEmpty()
			|| !mFunctionEqualities.getAllEquivalenceClasses().stream()
			.map(eqc -> eqc.contains(funcToBeHavocced))
			.reduce((a,b) -> a || b).get();
		mOwner.removeFunction(funcToBeHavocced);

//		// EDIT (22/06/2017): don't do any recursion because we call havoc on dependent nodes anyway
//		// call recursively on all functions depending on func
//		final Set<FUNCTION> dependentFunctions = 
//				mOwner.getAllFunctions().stream().filter(f -> f.dependsOn(func)).collect(Collectors.toSet());
//		for (FUNCTION f : dependentFunctions) {
//			havocFunction(f);
//		}
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

	/**
	 * 
	 * @return all equalities between functions that hold here, modulo symmetry, reflexivity --> might be expensive..
	 *    (used for simple implementation of flatten/merge/constraint set intersection)
	 */
	public Set<VPDomainSymmetricPair<FUNCTION>> getAllFunctionEqualities() {
		final Set<VPDomainSymmetricPair<FUNCTION>> result = new HashSet<>();
		for (Set<FUNCTION > eqc : mFunctionEqualities.getAllEquivalenceClasses()) {
			// TODO: naive implementation could do in little Gauss instead of n^2
			for (FUNCTION f1 : eqc) {
				for (FUNCTION f2 : eqc) {
					result.add(new VPDomainSymmetricPair<>(f1, f2));
				}
			}
			
		}
		return result;
	}

	/**
	 * analogue to getAllFunctionEqualities
	 * @return
	 */
	public Set<VPDomainSymmetricPair<FUNCTION>> getAllFunctionDisequalities() {
		final Set<VPDomainSymmetricPair<FUNCTION>> result = new HashSet<>();
		for (VPDomainSymmetricPair<FUNCTION> deq : mFunctionDisequalities) {
			for (FUNCTION f1 : mFunctionEqualities.getEquivalenceClassMembers(deq.getFirst())) {
				for (FUNCTION f2 : mFunctionEqualities.getEquivalenceClassMembers(deq.getSecond())) {
					result.add(new VPDomainSymmetricPair<>(f1, f2));
				}
			}
		}
		return result;
	}

	public boolean isEmpty() {
		//TODO could be done more efficiently
		return getAllFunctionEqualities().isEmpty() && getAllFunctionDisequalities().isEmpty(); 
	}

}
