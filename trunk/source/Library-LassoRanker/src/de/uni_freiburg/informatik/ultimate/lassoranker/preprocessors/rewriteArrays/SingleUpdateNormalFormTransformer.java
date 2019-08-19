/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.MultiElementCounter;



/**
 * Transform conjunction into equisatisfiable conjunction such that each multi-
 * dimensional store occurs only in a conjunction of the form
 * a' = (store a index value)
 * @author Matthias Heizmann
 *
 */
public class SingleUpdateNormalFormTransformer {
	
	static final String s_AuxArray = "auxArray";
	
	private final List<ArrayUpdate> mArrayUpdates;
	private List<Term> mRemainderTerms;
	private Map<Term, Term> mStore2TermVariable;
	private final Script mScript;
	private final FreshAuxVarGenerator mFreshAuxVarGenerator;
	
	public SingleUpdateNormalFormTransformer(final Term input, Script script,
			FreshAuxVarGenerator freshAuxVarGenerator) {
		mScript = script;
		mFreshAuxVarGenerator = freshAuxVarGenerator;
		mArrayUpdates = new ArrayList<ArrayUpdate>();
		final Term[] conjuncts = SmtUtils.getConjuncts(input);
		final ArrayUpdateExtractor aue = new ArrayUpdateExtractor(false, true, conjuncts);
		mRemainderTerms = aue.getRemainingTerms();
		mArrayUpdates.addAll(aue.getArrayUpdates());
		mStore2TermVariable = aue.getStore2TermVariable();
		
		while(true) {
			if (!mStore2TermVariable.isEmpty()) {
				processNewArrayUpdates();
			} else {
				// add only one new update in one iteration since there
				// might be terms of the form (store ...) = (store ...)
				final MultiDimensionalStore mdStore = extractStore(mArrayUpdates, mRemainderTerms);
				if (mdStore == null) {
					break;
				} else {
					processNewStore(mdStore);
				}
			}
		}
		assert mStore2TermVariable.isEmpty();
	}
	
	/**
	 * Construct auxiliary variable a_aux for store term.
	 * Add array update a_aux = mdStore to mArrayUpdates
	 * set mStore2TermVariable to (mdStore, a_aux);
	 */
	private void processNewStore(
			MultiDimensionalStore mdStore) {
		final Term oldArray = mdStore.getArray();
		TermVariable auxArray;
		auxArray = mFreshAuxVarGenerator.constructFreshCopy(oldArray); 
		assert mStore2TermVariable.isEmpty();
		mStore2TermVariable = 
				Collections.singletonMap((Term) mdStore.getStoreTerm(), (Term) auxArray);
		{
			final Term newUpdate = mScript.term("=", auxArray, mdStore.getStoreTerm());
			final ArrayUpdateExtractor aue = new ArrayUpdateExtractor(false, true, newUpdate);
			assert aue.getArrayUpdates().size() == 1;
			mArrayUpdates.add(aue.getArrayUpdates().get(0));
		}
	}
	
	/**
	 * Return some store term that is either in 
	 * <li> the index of one of the arrayUpdates
	 * <li> the value of one of the arrayUpdates
	 * <li> one of the remainderTerms
	 * Return null of no such store term exists.
	 */
	private MultiDimensionalStore extractStore(
			List<ArrayUpdate> arrayUpdates, List<Term> remainderTerms) {
		for (final ArrayUpdate au : arrayUpdates) {
			for (final Term entry : au.getIndex()) {
				final List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresDeep(entry);
				if (!mdStores.isEmpty()) {
					throw new AssertionError("not yet implemented");
				}
			}
			final List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresDeep(au.getValue());
			if (!mdStores.isEmpty()) {
				throw new AssertionError("not yet implemented");
			}
		}
		for (final Term term : remainderTerms) {
			final List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresDeep(term);
			if (!mdStores.isEmpty()) {
				return mdStores.get(0);
			}
		}
		return null;
	}
	
	private void processNewArrayUpdates() {
		final Substitution subst = new Substitution(mScript, mStore2TermVariable);
		for (final ArrayUpdate au : mArrayUpdates) {
			for (final Term entry : au.getIndex()) {
				final Term newEntry = subst.transform(entry);
				if (newEntry != entry) {
					throw new AssertionError("not yet implemented");
				}
			}
			final Term newValue =  subst.transform(au.getValue());
			if (newValue != au.getValue()) {
				throw new AssertionError("not yet implemented");
			}
		}
		final ArrayList<Term> newRemainderTerms = new ArrayList<Term>();
		final Map<Term, Term> newStore2TermVariable = new HashMap<Term, Term>();
		for (final Term term : mRemainderTerms) {
			final Term newTerm = subst.transform(term);
			final ArrayUpdateExtractor aue = new ArrayUpdateExtractor(false, true, newTerm);
			assert aue.getArrayUpdates().size() == 0 || aue.getArrayUpdates().size() == 1;
			if (aue.getArrayUpdates().isEmpty()) {
				newRemainderTerms.add(newTerm);
			} else {
				mArrayUpdates.addAll(aue.getArrayUpdates());
				newStore2TermVariable.putAll(aue.getStore2TermVariable());
			}
		}
		mRemainderTerms = newRemainderTerms;
		mStore2TermVariable = newStore2TermVariable;
		
	}
	
	private MultiDimensionalStore getNonUpdateStore(Term term) {
		final Term[] conjuncts = SmtUtils.getConjuncts(term);
		final ArrayUpdateExtractor aue = new ArrayUpdateExtractor(false, true, conjuncts);
		Term remainder = SmtUtils.and(mScript, aue.getRemainingTerms().toArray(new Term[0]));
		remainder = (new Substitution(mScript, aue.getStore2TermVariable())).transform(remainder);
		final List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresDeep(remainder);
		if (mdStores.isEmpty()) {
			return null;
		} else {
			return mdStores.get(0);
		}
	}
	
//	private Term addUpdate(MultiDimensionalStore arraryStore, Term term) {
//		Term oldArray = arraryStore.getArray();
//		TermVariable auxArray;
//		auxArray = constructAuxiliaryVariable(oldArray);
//		Map<Term, Term> substitutionMapping = 
//				Collections.singletonMap((Term) arraryStore.getStoreTerm(), (Term) auxArray);
//		Term newTerm = (new SafeSubstitution(mScript, substitutionMapping)).transform(term);
//		return SmtUtils.and(mScript, newTerm, mScript.term("=", auxArray, arraryStore.getStoreTerm()));
//	}

	public List<ArrayUpdate> getArrayUpdates() {
		return Collections.unmodifiableList(mArrayUpdates);
	}

	public Term getRemainderTerm() {
		return SmtUtils.and(mScript, mRemainderTerms.toArray(new Term[mRemainderTerms.size()]));
	}
	
	public Set<TermVariable> getAuxVars() {
		return mFreshAuxVarGenerator.getAuxVars();
	}
	
	public static class FreshAuxVarGenerator {
		private final Map<TermVariable, Term> mFreshCopyToOriginal = new HashMap<TermVariable, Term>();
		private final MultiElementCounter<Term> mFreshCopyCounter = new MultiElementCounter<>();
		private final ReplacementVarFactory mReplacementVarFactory;
		
		public FreshAuxVarGenerator(ReplacementVarFactory replacementVarFactory) {
			super();
			mReplacementVarFactory = replacementVarFactory;
		}

		TermVariable constructFreshCopy(Term term) {
			Term original = mFreshCopyToOriginal.get(term);
			if (original == null) {
				// no original Term known use term itself as original
				original = term;
			}
			final Integer numberOfFreshCopy = mFreshCopyCounter.increment(original);
			final String nameOfFreshCopy = SmtUtils.removeSmtQuoteCharacters(original.toString()) + s_AuxArray + numberOfFreshCopy;
			final TermVariable freshCopy = mReplacementVarFactory.getOrConstructAuxVar(nameOfFreshCopy, term.getSort());
			mFreshCopyToOriginal.put(freshCopy, original);
			return freshCopy;
			
		}
		
		public Set<TermVariable> getAuxVars() {
			return mFreshCopyToOriginal.keySet();
		}
	}
}
