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
import java.util.Iterator;
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ElimStore3.IndicesAndValues;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
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

	public ElimStorePlain(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		super();
		mQuantifier = QuantifiedFormula.EXISTS;
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
	}
	
	
	
	
	public Pair<Term, Collection<TermVariable>> elimAll(final Collection<TermVariable> inputEliminatees, final Term inputTerm) {
		
		AfEliminationTask eliminationTask = new AfEliminationTask(inputEliminatees, inputTerm);
		int numberOfRounds = 0;
		while (true) {
			final TreeRelation<Integer, TermVariable> tr = classifyEliminatees(eliminationTask.getEliminatees());
			final StringBuilder sb = new StringBuilder();
			for (final Integer dim : tr.getDomain()) {
				sb.append(tr.getImage(dim).size() + " variables of dimension " + dim + ", ");
			}
			mLogger.info("We have to eliminate " + sb.toString());
			
			final LinkedHashSet<TermVariable> eliminatees = getArrayTvSmallDimensionsFirst(tr);
			
			
			if (eliminatees.isEmpty()) {
				// no array eliminatees left
				break;
			}
			TermVariable thisIterationEliminatee;
			{
				final Iterator<TermVariable> it = eliminatees.iterator();
				thisIterationEliminatee = it.next();
				it.remove();
			}
			
			final AfEliminationTask elimRes = elim1(thisIterationEliminatee, eliminationTask.getTerm());
			eliminatees.addAll(elimRes.getEliminatees());
			eliminationTask = new AfEliminationTask(eliminatees, elimRes.getTerm());
			eliminationTask = applyNonSddEliminations(eliminationTask);
			
			numberOfRounds++;
		}
		mLogger.info("Needed " + numberOfRounds + " rounds to eliminate " + inputEliminatees.size() + " variables");
		// return term and variables that we could not eliminate
		return new Pair<>(eliminationTask.getTerm(), eliminationTask.getEliminatees());
	}




	private AfEliminationTask applyNonSddEliminations(final AfEliminationTask eliminationTask) throws AssertionError {
		final Term quantified = SmtUtils.quantifier(mScript, mQuantifier, eliminationTask.getEliminatees(), eliminationTask.getTerm());
		final Term pushed = new QuantifierPusher(mMgdScript, mServices, true, PqeTechniques.ALL_LOCAL).transform(quantified);

		final Term pnf = new PrenexNormalForm(mMgdScript).transform(pushed);
		final QuantifierSequence qs = new QuantifierSequence(mMgdScript.getScript(), pnf);
		final Term matrix = qs.getInnerTerm();
		final List<QuantifiedVariables> qvs = qs.getQuantifierBlocks();

		final Collection<TermVariable> eliminatees1;
		if (qvs.size() == 0) {
			eliminatees1 = Collections.emptySet();
		} else if (qvs.size() == 1) {
			eliminatees1 = qvs.get(0).getVariables();
		} else if (qvs.size() > 1) {
			throw new UnsupportedOperationException("alternation not yet supported");
		} else {
			throw new AssertionError();
		}
		return new AfEliminationTask(eliminatees1, matrix);
	}




	private LinkedHashSet<TermVariable> getArrayTvSmallDimensionsFirst(final TreeRelation<Integer, TermVariable> tr) {
		final LinkedHashSet<TermVariable> result = new LinkedHashSet<>();
		for (final Integer dim : tr.getDomain()) {
			if (dim != 0) {
				result.addAll(tr.getImage(dim));
			}
		}
		return result;
	}


	private TreeRelation<Integer, TermVariable> classifyEliminatees(final Collection<TermVariable> eliminatees) {
		final TreeRelation<Integer, TermVariable> tr = new TreeRelation<>();
		for (final TermVariable eliminatee : eliminatees) {
			final MultiDimensionalSort mds = new MultiDimensionalSort(eliminatee.getSort());
			tr.addPair(mds.getDimension(), eliminatee);
		}
		return tr;
	}

	public AfEliminationTask elim1(final TermVariable eliminatee, final Term inputTerm) {
		final List<MultiDimensionalStore> stores = extractStores(eliminatee, inputTerm);
		if (stores.size() > 1) {
			throw new AssertionError("not yet supported");
		}
		final List<MultiDimensionalSelect> selects = extractSelects(eliminatee, inputTerm);
		
		final int quantifier = QuantifiedFormula.EXISTS;
		
		final List<ApplicationTerm> selectTerms = extractSelects2(eliminatee, inputTerm);
		
		
		if (false && stores.isEmpty()) {
			if (!selectTerms.isEmpty()) {
				final IndicesAndValues iav = new IndicesAndValues(mMgdScript, quantifier, eliminatee, inputTerm);
				final Pair<List<ArrayIndex>, List<Term>> indicesAndValues = ElimStore3.buildIndicesAndValues(mMgdScript, iav);

				final ArrayList<Term> indexValueConstraintsFromEliminatee = ElimStore3.constructIndexValueConstraints(
						mMgdScript.getScript(), quantifier, indicesAndValues.getFirst(), indicesAndValues.getSecond());
				final Term indexValueConstraints = PartialQuantifierElimination.applyDualFiniteConnective(mScript, mQuantifier,
						indexValueConstraintsFromEliminatee);
				final Substitution subst = new SubstitutionWithLocalSimplification(mMgdScript, iav.getMapping());
				final Term replaced = subst.transform(inputTerm);
				final Term result = SmtUtils.and(mScript, Arrays.asList(new Term[] { replaced, indexValueConstraints }));
				assert !Arrays.asList(result.getFreeVars()).contains(eliminatee) : "var is still there";
				return new AfEliminationTask(iav.getNewAuxVars(), result);
			} else {
				throw new AssertionError("no case applies");
			}
		}
		
		final Term storeTerm;
		final Term storeIndex;
		final Term storeValue;
		if (stores.isEmpty()) {
			storeTerm = null;
			storeIndex = null;
			storeValue = null;
			mLogger.info("store-free iteration");
		} else {
			final MultiDimensionalStore store = stores.iterator().next();
			storeTerm = store.getStoreTerm();
			storeIndex = store.getIndex().get(0);
			storeValue = ((ApplicationTerm) storeTerm).getParameters()[2];
			mLogger.info("eliminating store to array of dimension " + new MultiDimensionalSort(eliminatee.getSort()).getDimension());
		}
		
		final UnionFind<Term> indices = new UnionFind<>();
		if (!stores.isEmpty()) {
			indices.findAndConstructEquivalenceClassIfNeeded(storeIndex);
		}
		for (final ApplicationTerm entry : selectTerms) {
			indices.findAndConstructEquivalenceClassIfNeeded(getIndexOfSelect(entry));
		}
		final HashRelation<Term, Term> disjointIndices = new HashRelation<>();
		
		
		final List<Term> oldCellDefinitions = new ArrayList<>();
		final Set<TermVariable> newAuxVars = new LinkedHashSet<>(); 
		final Map<Term, TermVariable> oldCellMapping = constructOldCellValueMapping(selectTerms, indices, storeIndex, disjointIndices);
		for (final Entry<Term, TermVariable> entry : oldCellMapping.entrySet()) {
			newAuxVars.add(entry.getValue());
		}

		final Map<Term, Term> indexMapping = new HashMap<>();
		final List<Term> indexMappingDefinitions = new ArrayList<>();
		if (!stores.isEmpty()) {
			constructIndexReplacementIfNecessary(eliminatee, newAuxVars, indexMapping, indexMappingDefinitions, storeIndex);
		}
//		if (indexMapping.containsKey(storeIndex)) {
//			storeIndex = indexMapping.get(storeIndex);
//		}
		for (final ApplicationTerm entry : selectTerms) {
			final Term index = getIndexOfSelect(entry);
			constructIndexReplacementIfNecessary(eliminatee, newAuxVars, indexMapping, indexMappingDefinitions, index);
		}
		final Term indexDefinitionsTerm = SmtUtils.and(mScript, indexMappingDefinitions);
		final Term term = SmtUtils.and(mScript, Arrays.asList(new Term[]{indexDefinitionsTerm, inputTerm}));
		
		final TermVariable newAuxArray =
				mMgdScript.constructFreshTermVariable(s_AUX_VAR_NEW_ARRAY, eliminatee.getSort());
		newAuxVars.add(newAuxArray) ;
		
		final List<Term> disjuncts = new ArrayList<>();
		final CombinationIterator ci = new CombinationIterator(indices, disjointIndices);
		mLogger.info("Considering " + ci.size() + " cases while eliminating array variable of dimension " + new MultiDimensionalSort(eliminatee.getSort()).getDimension());
		for (final Set<Doubleton<Term>> equalDoubletons : ci) {
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			substitutionMapping.put(storeTerm, newAuxArray);
			final List<Term> indexEqualityTerms = new ArrayList<>();
			final List<Term> valueEqualityTerms = new ArrayList<>();
			for (final Doubleton<Term> doubleton : CombinationIterator.buildListOfNonDisjointDoubletons(indices, disjointIndices)) {
				final Term indexEqualityTerm;
				if (equalDoubletons.contains(doubleton)) {
					indexEqualityTerm = SmtUtils.binaryEquality(mScript, getNewIndex(doubleton.getOneElement(), indexMapping, eliminatee), getNewIndex(doubleton.getOtherElement(), indexMapping, eliminatee));
					final Term oneOldCellVariable = oldCellMapping.get(doubleton.getOneElement());
					final Term otherOldCellVariable = oldCellMapping.get(doubleton.getOtherElement());
					if (oneOldCellVariable != null && otherOldCellVariable != null) {
						final Term valueEqualityTerm = SmtUtils.binaryEquality(mScript, oneOldCellVariable, otherOldCellVariable);
						valueEqualityTerms.add(valueEqualityTerm);
					}
				} else {
					indexEqualityTerm = SmtUtils.distinct(mScript, getNewIndex(doubleton.getOneElement(), indexMapping, eliminatee), getNewIndex(doubleton.getOtherElement(), indexMapping, eliminatee));
				}
				indexEqualityTerms.add(indexEqualityTerm);
			}
			
			for (final ApplicationTerm selectTerm : selectTerms) {
				final Term indexOfSelect = getIndexOfSelect(selectTerm); 
				final boolean selectIndexEquivalentToStoreIndex;
				if (stores.isEmpty()) {
					selectIndexEquivalentToStoreIndex = true;
				} else {
					selectIndexEquivalentToStoreIndex = 
						indices.find(indexOfSelect).equals(indices.find(storeIndex)) || 
						equalDoubletons.contains(new Doubleton<Term>(indexOfSelect, storeIndex)) ||  
						equalDoubletons.contains(new Doubleton<Term>(storeIndex, indexOfSelect));
				}
				if (selectIndexEquivalentToStoreIndex) {
					final Term oldCell = oldCellMapping.get(indexOfSelect);
					assert oldCell != null;
					substitutionMapping.put(selectTerm, oldCell);
				} else {
					final Term newSelect = constructNewSelectWithPossiblyReplacedIndex(newAuxArray, selectTerm, indexMapping, eliminatee);
					assert !Arrays.asList(newSelect.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee;
					substitutionMapping.put(selectTerm, newSelect);
				}
			}
			
			final Term storedValueInformation;
			if (stores.isEmpty()) {
				storedValueInformation = mScript.term("true");
			} else {
				storedValueInformation = SmtUtils.binaryEquality(mScript, 
					mScript.term("select", newAuxArray, getNewIndex(storeIndex, indexMapping, eliminatee)), 
					new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(storeValue));
			}
			
			Term disjuct = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(term);
			
			disjuct = Util.and(mScript, SmtUtils.and(mScript, indexEqualityTerms), SmtUtils.and(mScript, valueEqualityTerms), disjuct, storedValueInformation);
			assert !Arrays.asList(disjuct.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee;
			disjuncts.add(disjuct);
			
		}

		final Term result = SmtUtils.or(mScript, disjuncts);
		if (Arrays.asList(result.getFreeVars()).contains(eliminatee)) {
			throw new AssertionError("var is still there " + eliminatee + "  quantifier " + result + "  term size "
					+ (new DagSizePrinter(term)) + "   " + term);
		}
		return new AfEliminationTask(newAuxVars, result);
		
	}




	private void constructIndexReplacementIfNecessary(final TermVariable eliminatee, final Set<TermVariable> newAuxVars,
			final Map<Term, Term> indexMapping, final List<Term> indexMappingDefinitions, final Term index) {
		if (Arrays.asList(index.getFreeVars()).contains(eliminatee)) {
			// need to replace index
			final TermVariable newAuxIndex =
					mMgdScript.constructFreshTermVariable(s_AUX_VAR_INDEX, index.getSort());
			newAuxVars.add(newAuxIndex);
			indexMapping.put(index, newAuxIndex);
			indexMappingDefinitions.add(SmtUtils.binaryEquality(mScript, newAuxIndex, index));
		}
	}

	private Term constructNewSelectWithPossiblyReplacedIndex(final TermVariable newAuxArray,
			final ApplicationTerm oldSelectTerm, final Map<Term, Term> indexMapping, final TermVariable eliminatee) {
		final Term newIndex = getPossiblyReplacedIndex(oldSelectTerm, indexMapping, eliminatee);
		final Term newSelect = mMgdScript.getScript().term("select", newAuxArray, newIndex);
		return newSelect;
	}




	private Term getPossiblyReplacedIndex(final ApplicationTerm oldSelectTerm, final Map<Term, Term> indexMapping, final TermVariable eliminatee) {
		return getNewIndex(getIndexOfSelect(oldSelectTerm), indexMapping, eliminatee);
	}
	
	private Term getNewIndex(final Term originalIndex, final Map<Term, Term> indexMapping, final TermVariable eliminatee) {
		final Term newIndex;
		final Term replacementIndex = indexMapping.get(originalIndex);
		if (replacementIndex == null) {
			newIndex = originalIndex;
			assert !Arrays.asList(originalIndex.getFreeVars()).contains(eliminatee);
		} else {
			newIndex = replacementIndex;
			assert Arrays.asList(originalIndex.getFreeVars()).contains(eliminatee);
		}
		return newIndex;
	}
	

	private Map<Term, TermVariable> constructOldCellValueMapping(final List<ApplicationTerm> equivalentIndex,
			final UnionFind<Term> indices, final Term storeIndex, final HashRelation<Term, Term> disjointIndices) throws AssertionError {
		final Map<Term, TermVariable> oldCellMapping = new HashMap<>();
		for (final ApplicationTerm selectTerm : equivalentIndex) {
			final Term selectIndex = getIndexOfSelect(selectTerm);
			if (disjointIndices.containsPair(selectIndex, storeIndex)) {
				// do nothing
			} else {
				constructAndAddOldCellValueTermVariable(oldCellMapping, selectTerm, indices);
			}
		}
		return oldCellMapping;
	}

	private void constructAndAddOldCellValueTermVariable(final Map<Term, TermVariable> oldCellMapping,
			final ApplicationTerm entry, final UnionFind<Term> indices) throws AssertionError {
		final Term indexRepresentative = indices.find(getIndexOfSelect(entry));
		TermVariable oldCell = oldCellMapping.get(indexRepresentative);
		if (oldCell == null) {
			oldCell = mMgdScript.constructFreshTermVariable(s_AUX_VAR_ARRAYCELL, entry.getSort());
			final Term oldValue = oldCellMapping.put(indexRepresentative, oldCell);
			if (oldValue != null) {
				throw new AssertionError("must not insert twice");
			}

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
	
	
	private static class CombinationIterator implements Iterable<Set<Doubleton<Term>>> {
		
		private final List<Set<Doubleton<Term>>> mResult = new ArrayList<>();
		
		public CombinationIterator(final UnionFind<Term> indices, final HashRelation<Term, Term> disjointIndices) {
			super();
			final List<Doubleton<Term>> doubeltons = buildListOfNonDisjointDoubletons(indices, disjointIndices);
			
			final int[] numberOfValues = new int[doubeltons.size()];
			Arrays.fill(numberOfValues, 2);
			final LexicographicCounter lc = new LexicographicCounter(numberOfValues);
			
			do {
				final HashRelation<Term, Term> relationCandidate = new HashRelation<>();
				for (final Term index : indices.getAllRepresentatives()) {
					relationCandidate.addPair(index, index);
				}
				final Set<Doubleton<Term>> resultCandidate = new HashSet<>();
				for (int i = 0; i < doubeltons.size(); i++) {
					if (lc.getCurrentValue()[i] == 1) {
						final Doubleton<Term> doubleton = doubeltons.get(i);
						relationCandidate.addPair(doubleton.getOneElement(), doubleton.getOtherElement());
						relationCandidate.addPair(doubleton.getOtherElement(), doubleton.getOneElement());
						resultCandidate.add(doubleton);
					}
				}
				if (isClosedUnderTransitivity(relationCandidate)) {
					mResult.add(resultCandidate);
				}
				
				lc.increment();
			} while (!lc.isZero());
		}
		
		public int size() {
			return mResult.size();
		}






		public static <E> boolean isClosedUnderTransitivity(final HashRelation<E, E> relation) {
			for (final Entry<E, E> entry : relation.entrySet()) {
				for (final E image : relation.getImage(entry.getValue())) {
					if (!relation.containsPair(entry.getKey(), image)) {
						return false;
					}
				}
			}
			return true;
		}






		public static List<Doubleton<Term>> buildListOfNonDisjointDoubletons(final UnionFind<Term> indices, 
				final HashRelation<Term, Term> disjointIndices) {
			final List<Doubleton<Term>> doubeltons = new ArrayList<>();
			final List<Term> indexList = new ArrayList<Term>(indices.getAllRepresentatives());
			for (int i = 0; i < indexList.size(); i++) {
				for (int j = i+1; j < indexList.size(); j++) {
					if (!disjointIndices.containsPair(indexList.get(i), indexList.get(j))) {
						doubeltons.add(new Doubleton<Term>(indexList.get(i), indexList.get(j)));
					}
				}
			}
			return doubeltons;
		}
		
		

		@Override
		public Iterator<Set<Doubleton<Term>>> iterator() {
			return mResult.iterator();
		}
		
		
		
	}
	
	/**
	 * Alternation-free (quantifier) elimination task
	 *
	 */
	private static class AfEliminationTask {
		private final Collection<TermVariable> mEliminatees;
		private final Term mTerm;
		public AfEliminationTask(final Collection<TermVariable> eliminatees, final Term term) {
			super();
			mEliminatees = eliminatees;
			mTerm = term;
		}
		public Collection<TermVariable> getEliminatees() {
			return mEliminatees;
		}
		public Term getTerm() {
			return mTerm;
		}
		
		
		
	}

}
