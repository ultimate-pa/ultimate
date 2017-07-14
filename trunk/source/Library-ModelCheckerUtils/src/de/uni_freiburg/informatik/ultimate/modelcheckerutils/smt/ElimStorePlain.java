/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.LexicographicCounter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeRelation;

/**
 *
 * 
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ElimStorePlain {

	private final int mQuantifier;
	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final static String s_AUX_VAR_NEW_ARRAY = "arrayElimArr";
	private final static String s_AUX_VAR_INDEX = "arrayElimIndex";
	private final static String s_AUX_VAR_ARRAYCELL = "arrayElimCell";

	public ElimStorePlain(final Script script, final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		super();
		mQuantifier = QuantifiedFormula.EXISTS;
		mScript = script;
		mMgdScript = mgdScript;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
	}
	
	
	
	
	public Pair<Term, Collection<TermVariable>> elimAll(final Collection<TermVariable> inputEliminatees, final Term inputTerm) {
		
		Collection<TermVariable> eliminatees = inputEliminatees;
		Term term = inputTerm;
		while (true) {
			final TreeRelation<Integer, TermVariable> tr = classifyEliminatees(eliminatees);
			eliminatees = new HashSet<>();
			TermVariable thisIterationEliminatee = null;
			for (final Integer dim : tr.getDomain()) {
				for (final TermVariable var : tr.getImage(dim)) {
					if (dim > 0 && thisIterationEliminatee == null) {
						thisIterationEliminatee = var;
					} else {
						eliminatees.add(var);
					}
				}
			}
			if (thisIterationEliminatee == null) {
				// no array eliminatees left
				break;
			}
			final Pair<Term, Set<TermVariable>> elimRes = elim1(thisIterationEliminatee, term);
			term = elimRes.getFirst();
			eliminatees.addAll(elimRes.getSecond());
			final Term quantified = SmtUtils.quantifier(mScript, mQuantifier, eliminatees, term);
			final Term pushed = new QuantifierPusher(mMgdScript, mServices, true, PqeTechniques.ALL_LOCAL).transform(quantified);
			
			final Term pnf = new PrenexNormalForm(mMgdScript).transform(pushed);
			final QuantifierSequence qs = new QuantifierSequence(mMgdScript.getScript(), pnf);
			final Term matrix = qs.getInnerTerm();
			final List<QuantifiedVariables> qvs = qs.getQuantifierBlocks();
			if (qvs.size() == 0) {
				eliminatees = Collections.emptySet();
			} else if (qvs.size() == 1) {
				eliminatees = qvs.get(0).getVariables();
			} else if (qvs.size() > 1) {
				throw new UnsupportedOperationException("alternation not yet supported");
			}
			term = matrix;

		}
		// return term and variables that we could not eliminate
		return new Pair<>(term, eliminatees);
	}


	private TreeRelation<Integer, TermVariable> classifyEliminatees(final Collection<TermVariable> eliminatees) {
		final TreeRelation<Integer, TermVariable> tr = new TreeRelation<>();
		for (final TermVariable eliminatee : eliminatees) {
			final MultiDimensionalSort mds = new MultiDimensionalSort(eliminatee.getSort());
			tr.addPair(mds.getDimension(), eliminatee);
		}
		return tr;
	}

	public Pair<Term, Set<TermVariable>> elim1(final TermVariable eliminatee, final Term inputTerm) {
		final List<MultiDimensionalStore> stores = extractStores(eliminatee, inputTerm);
		if (stores.size() > 1) {
			throw new AssertionError("not yet supported");
		}
		final MultiDimensionalStore store = stores.iterator().next();
		final Term storeIndex = store.getIndex().get(0);
		final List<MultiDimensionalSelect> selects = extractSelects(eliminatee, inputTerm);
		
		final List<ApplicationTerm> equivalentIndex = Collections.emptyList();
		final List<ApplicationTerm> distinctIndex = Collections.emptyList();
		final List<ApplicationTerm> unknownIndex = extractSelects2(eliminatee, inputTerm);
		
		final List<Term> oldCellDefinitions = new ArrayList<>();
		final Set<TermVariable> newAuxVars = new LinkedHashSet<>(); 
		final Map<ApplicationTerm, TermVariable> oldCellMapping = constructOldCellValueMapping(equivalentIndex,
				unknownIndex);
		for (final Entry<ApplicationTerm, TermVariable> entry : oldCellMapping.entrySet()) {
			newAuxVars.add(entry.getValue());
			oldCellDefinitions.add(SmtUtils.binaryEquality(mScript, entry.getValue(), entry.getKey()));
		}
		final Term oldCellDefinitionsTerm = SmtUtils.and(mScript, oldCellDefinitions);

		
		
		final int[] numberOfValues = new int[unknownIndex.size()];
		Arrays.fill(numberOfValues, 2);
		final LexicographicCounter lc = new LexicographicCounter(numberOfValues);

		
		final Map<Term, Term> indexMapping = new HashMap<>();
		final List<Term> indexMappingDefinitions = new ArrayList<>();
		for (final ApplicationTerm entry : unknownIndex) {
			final Term index = getIndexOfSelect(entry);
			if (Arrays.asList(index.getFreeVars()).contains(eliminatee)) {
				// need to replace index
				final TermVariable newAuxIndex =
						mMgdScript.constructFreshTermVariable(s_AUX_VAR_INDEX, entry.getSort());
				newAuxVars.add(newAuxIndex);
				indexMapping.put(index, newAuxIndex);
				indexMappingDefinitions.add(SmtUtils.binaryEquality(mScript, newAuxIndex, index));
			}
		}
		final Term indexDefinitionsTerm = SmtUtils.and(mScript, indexMappingDefinitions);
		final Term term = SmtUtils.and(mScript, Arrays.asList(new Term[]{indexDefinitionsTerm, oldCellDefinitionsTerm, inputTerm}));
		
		final TermVariable newAuxArray =
				mMgdScript.constructFreshTermVariable(s_AUX_VAR_NEW_ARRAY, eliminatee.getSort());
		newAuxVars.add(newAuxArray) ;
		
		final List<Term> disjuncts = new ArrayList<>();
		do {
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			substitutionMapping.put(store.getStoreTerm(), newAuxArray);
			for (final ApplicationTerm entry : equivalentIndex) {
				final Term newSelect = oldCellMapping.get(entry);
				assert !Arrays.asList(newSelect.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee;
				substitutionMapping.put(entry, newSelect);
			}
			for (final ApplicationTerm entry : distinctIndex) {
				final Term newSelect = constructNewSelectWithPossiblyReplacedIndex(newAuxArray, entry, indexMapping);
				assert !Arrays.asList(newSelect.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee;
				substitutionMapping.put(entry, newSelect);
			}
			final List<Term> indexEqualityTerms = new ArrayList<>();
			int offset = 0;
			for (final ApplicationTerm entry : unknownIndex) {
				final Term indexEqualityTerm;
				if (lc.getCurrentValue()[offset] == 0) {
					// equal
					indexEqualityTerm = SmtUtils.binaryEquality(mScript, storeIndex, getIndexOfSelect(entry));
					final Term newSelect = oldCellMapping.get(entry);
					assert !Arrays.asList(newSelect.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee;
					substitutionMapping.put(entry, newSelect);
				} else {
					// different
					indexEqualityTerm = SmtUtils.distinct(mScript, storeIndex, getIndexOfSelect(entry));
					final Term newSelect = constructNewSelectWithPossiblyReplacedIndex(newAuxArray, entry, indexMapping);
					assert !Arrays.asList(newSelect.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee;
					substitutionMapping.put(entry, newSelect);
				}
				offset++;
				
				indexEqualityTerms.add(indexEqualityTerm);
			}
			final Term newSelect = SmtUtils.binaryEquality(mScript, 
					mScript.term("select", newAuxArray, storeIndex), 
					new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(store.getStoreTerm().getParameters()[2]));
			
			Term disjuct = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(term);
			
			disjuct = Util.and(mScript, SmtUtils.and(mScript, indexEqualityTerms), disjuct, newSelect);
			assert !Arrays.asList(disjuct.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee;
			disjuncts.add(disjuct);
			
			lc.increment();
		} while (!lc.isZero());
		final Term result = SmtUtils.or(mScript, disjuncts);
		if (Arrays.asList(result.getFreeVars()).contains(eliminatee)) {
			throw new AssertionError("var is still there " + eliminatee + "  quantifier " + result + "  term size "
					+ (new DagSizePrinter(term)) + "   " + term);
		}
		return new Pair<Term, Set<TermVariable>>(result, newAuxVars);
		
	}

	private Term constructNewSelectWithPossiblyReplacedIndex(final TermVariable newAuxArray,
			final ApplicationTerm oldSelectTerm, final Map<Term, Term> indexMapping) {
		final Term newIndex;
		final Term originalIndex = getIndexOfSelect(oldSelectTerm);
		final Term replacementIndex = indexMapping.get(originalIndex);
		if (replacementIndex == null) {
			newIndex = originalIndex;
		} else {
			newIndex = replacementIndex;
		}
		final Term newSelect = mMgdScript.getScript().term("select", newAuxArray, newIndex);
		return newSelect;
	}

	private Map<ApplicationTerm, TermVariable> constructOldCellValueMapping(final List<ApplicationTerm> equivalentIndex,
			final List<ApplicationTerm> unknownIndex) throws AssertionError {
		final Map<ApplicationTerm, TermVariable> oldCellMapping = new HashMap<>();
		for (final ApplicationTerm entry : equivalentIndex) {
			constructAndAddOldCellValueTermVariable(oldCellMapping, entry);
		}
		for (final ApplicationTerm entry : unknownIndex) {
			constructAndAddOldCellValueTermVariable(oldCellMapping, entry);
		}
		return oldCellMapping;
	}

	private void constructAndAddOldCellValueTermVariable(final Map<ApplicationTerm, TermVariable> oldCellMapping,
			final ApplicationTerm entry) throws AssertionError {
		final TermVariable oldCell = mMgdScript.constructFreshTermVariable(s_AUX_VAR_ARRAYCELL, entry.getSort());
		final TermVariable oldValue = oldCellMapping.put(entry, oldCell);
		if (oldValue != null) {
			throw new AssertionError("must not insert twice");
		}
	}
	
	private Term getIndexOfSelect(final ApplicationTerm appTerm) {
		assert (appTerm.getParameters().length == 2) : "no select";
		assert (appTerm.getFunction().getName().equals("select")) : "no select";
		return appTerm.getParameters()[1];
	}

	private List<MultiDimensionalStore> extractStores(final TermVariable eliminatee, final Term term) {
		final List<MultiDimensionalStore> result = new ArrayList<>();
		final Set<ApplicationTerm> stores = new ApplicationTermFinder("store", false).findMatchingSubterms(term);
		for (final ApplicationTerm appTerm : stores) {
			if (appTerm.getParameters()[0].equals(eliminatee)) {
				result.add(new MultiDimensionalStore(appTerm));
			}
		}
		return result;
	}
	
	private List<MultiDimensionalSelect> extractSelects(final TermVariable eliminatee, final Term term) {
		final List<MultiDimensionalSelect> result = new ArrayList<>();
		final Set<ApplicationTerm> stores = new ApplicationTermFinder("select", false).findMatchingSubterms(term);
		for (final ApplicationTerm appTerm : stores) {
			if (appTerm.getParameters()[0].equals(eliminatee)) {
				result.add(new MultiDimensionalSelect(appTerm));
			}
		}
		return result;
	}
	
	private List<ApplicationTerm> extractSelects2(final TermVariable eliminatee, final Term term) {
		final List<ApplicationTerm> result = new ArrayList<>();
		final Set<ApplicationTerm> stores = new ApplicationTermFinder("select", false).findMatchingSubterms(term);
		for (final ApplicationTerm appTerm : stores) {
			if (appTerm.getParameters()[0].equals(eliminatee)) {
				result.add(appTerm);
			}
		}
		return result;
	}

}
