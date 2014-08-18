/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoBuilder;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;


/**
 * Transform conjunction into equisatisfiable conjunction such that each multi-
 * dimensional store occurs only in a conjunction of the form
 * a' = (store a index value)
 * @author Matthias Heizmann
 *
 */
public class SingleUpdateNormalFormTransformer {
	
	static final String s_AuxArray = "auxArray";
	
	private final List<ArrayUpdate> m_ArrayUpdates;
	private List<Term> m_RemainderTerms;
	private Map<Term, Term> m_Store2TermVariable;
	private final Script m_Script;
	private final LassoBuilder m_lassoBuilder;
	
	public SingleUpdateNormalFormTransformer(final Term input, Script script,
			LassoBuilder lassoBuilder) {
		m_Script = script;
		m_lassoBuilder = lassoBuilder;
		m_ArrayUpdates = new ArrayList<ArrayUpdate>();
		Term[] conjuncts = SmtUtils.getConjuncts(input);
		ArrayUpdateExtractor aue = new ArrayUpdateExtractor(conjuncts);
		m_RemainderTerms = aue.getRemainingTerms();
		m_ArrayUpdates.addAll(aue.getArrayUpdates());
		m_Store2TermVariable = aue.getStore2TermVariable();
		
		while(true) {
			if (!m_Store2TermVariable.isEmpty()) {
				processNewArrayUpdates();
			} else {
				// add only one new update in one iteration since there
				// might be terms of the form (store ...) = (store ...)
				MultiDimensionalStore mdStore = extractStore(m_ArrayUpdates, m_RemainderTerms);
				if (mdStore == null) {
					break;
				} else {
					processNewStore(mdStore);
				}
			}
		}
		assert m_Store2TermVariable.isEmpty();
	}
	
	/**
	 * Construct auxiliary variable a_aux for store term.
	 * Add array update a_aux = mdStore to m_ArrayUpdates
	 * set m_Store2TermVariable to (mdStore, a_aux);
	 */
	private void processNewStore(
			MultiDimensionalStore mdStore) {
		Term oldArray = mdStore.getArray();
		TermVariable auxArray;
		auxArray = constructAuxiliaryVariable(oldArray);
		assert m_Store2TermVariable.isEmpty();
		m_Store2TermVariable = 
				Collections.singletonMap((Term) mdStore.getStoreTerm(), (Term) auxArray);
		{
			Term newUpdate = m_Script.term("=", auxArray, mdStore.getStoreTerm());
			ArrayUpdateExtractor aue = new ArrayUpdateExtractor(newUpdate);
			assert aue.getArrayUpdates().size() == 1;
			m_ArrayUpdates.add(aue.getArrayUpdates().get(0));
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
		for (ArrayUpdate au : arrayUpdates) {
			for (Term entry : au.getIndex()) {
				List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresDeep(entry);
				if (!mdStores.isEmpty()) {
					throw new AssertionError("not yet implemented");
				}
			}
			List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresDeep(au.getValue());
			if (!mdStores.isEmpty()) {
				throw new AssertionError("not yet implemented");
			}
		}
		for (Term term : remainderTerms) {
			List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresDeep(term);
			if (!mdStores.isEmpty()) {
				return mdStores.get(0);
			}
		}
		return null;
	}
	
	private void processNewArrayUpdates() {
		SafeSubstitution subst = new SafeSubstitution(m_Script, m_Store2TermVariable);
		for (ArrayUpdate au : m_ArrayUpdates) {
			for (Term entry : au.getIndex()) {
				Term newEntry = subst.transform(entry);
				if (newEntry != entry) {
					throw new AssertionError("not yet implemented");
				}
			}
			Term newValue =  subst.transform(au.getValue());
			if (newValue != au.getValue()) {
				throw new AssertionError("not yet implemented");
			}
		}
		ArrayList<Term> newRemainderTerms = new ArrayList<Term>();
		Map<Term, Term> newStore2TermVariable = new HashMap<Term, Term>();
		for (Term term : m_RemainderTerms) {
			Term newTerm = subst.transform(term);
			ArrayUpdateExtractor aue = new ArrayUpdateExtractor(newTerm);
			assert aue.getArrayUpdates().size() == 0 || aue.getArrayUpdates().size() == 1;
			if (aue.getArrayUpdates().isEmpty()) {
				newRemainderTerms.add(newTerm);
			} else {
				m_ArrayUpdates.addAll(aue.getArrayUpdates());
				newStore2TermVariable.putAll(aue.getStore2TermVariable());
			}
		}
		m_RemainderTerms = newRemainderTerms;
		m_Store2TermVariable = newStore2TermVariable;
		
	}
	
	private MultiDimensionalStore getNonUpdateStore(Term term) {
		Term[] conjuncts = SmtUtils.getConjuncts(term);
		ArrayUpdateExtractor aue = new ArrayUpdateExtractor(conjuncts);
		Term remainder = Util.and(m_Script, aue.getRemainingTerms().toArray(new Term[0]));
		remainder = (new SafeSubstitution(m_Script, aue.getStore2TermVariable())).transform(remainder);
		List<MultiDimensionalStore> mdStores = MultiDimensionalStore.extractArrayStoresDeep(remainder);
		if (mdStores.isEmpty()) {
			return null;
		} else {
			return mdStores.get(0);
		}
	}
	
	private Term addUpdate(MultiDimensionalStore arraryStore, Term term) {
		Term oldArray = arraryStore.getArray();
		TermVariable auxArray;
		auxArray = constructAuxiliaryVariable(oldArray);
		Map<Term, Term> substitutionMapping = 
				Collections.singletonMap((Term) arraryStore.getStoreTerm(), (Term) auxArray);
		Term newTerm = (new SafeSubstitution(m_Script, substitutionMapping)).transform(term);
		return Util.and(m_Script, newTerm, m_Script.term("=", auxArray, arraryStore.getStoreTerm()));
	}

	private TermVariable constructAuxiliaryVariable(Term oldArray) {
		String name = SmtUtils.removeSmtQuoteCharacters(oldArray.toString() + s_AuxArray); 
		TermVariable auxArray = 
				m_lassoBuilder.getNewTermVariable(name, oldArray.getSort());
		return auxArray;
	}

	public List<ArrayUpdate> getArrayUpdates() {
		return Collections.unmodifiableList(m_ArrayUpdates);
	}

	public Term getRemainderTerm() {
		return Util.and(m_Script, m_RemainderTerms.toArray(new Term[m_RemainderTerms.size()]));
	}
}