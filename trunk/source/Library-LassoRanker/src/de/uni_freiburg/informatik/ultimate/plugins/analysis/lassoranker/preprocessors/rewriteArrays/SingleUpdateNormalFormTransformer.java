package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors.rewriteArrays;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.VarFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SafeSubstitution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;


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
	private final VarFactory m_VarFactory;

	public SingleUpdateNormalFormTransformer(final Term input, Script script,
			VarFactory varFactory) {
		m_Script = script;
		m_VarFactory = varFactory;
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
				m_VarFactory.getNewTermVariable(name, oldArray.getSort());
		return auxArray;
	}

	public List<ArrayUpdate> getArrayUpdates() {
		return Collections.unmodifiableList(m_ArrayUpdates);
	}

	public Term getRemainderTerm() {
		return Util.and(m_Script, m_RemainderTerms.toArray(new Term[m_RemainderTerms.size()]));
	}
}