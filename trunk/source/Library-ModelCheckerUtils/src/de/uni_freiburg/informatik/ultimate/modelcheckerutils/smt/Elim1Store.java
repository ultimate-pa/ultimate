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
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IncrementalPlicationChecker.Plication;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArraySelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArraySelectOverStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelectOverStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.EqualityInformation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Let aElim be the array variable that we want to eliminate. We presume that
 * there is only one term of the form (store aElim storeIndex newValue), for
 * some index element storeIndex and some value element newValue.
 *
 * The basic idea is the following. Let Idx be the set of all indices of select
 * terms that have aElim as (first) argument. We introduce
 * <ul>
 * <li>a new array variable aNew that represents the store term
 * <li>a new value variable oldCell_i for each i∈Idx that represents the value
 * of the array cell before the update.
 * </ul>
 * We replace
 * <ul>
 * <li>(store aElim storeIndex newValue) by aNew, and
 * <li>(select aElim i) by oldCell_i for each i∈Idx.
 * </ul>
 * Furthermore, we add the following conjuncts for each i∈Idx. 
 * <ul>
 * <li> (i == storeIndex)==> (aNew[i] == newValue && ∀k∈Idx. i == k ==> oldCell_i == oldCell_k) 
 * <li> (i != storeIndex) ==> (aNew[i] == oldCell_i)
 * </ul>
 * 
 * Optimizations: 
 * <ul>
 * <li> Optim1: We check equality and disequality for each pair of
 * indices and evaluate (dis)equalities in the formula above directly. Each
 * equality/disequality that is not valid (i.e. only true in this context) has
 * to be added as an additional conjunct.
 * <li> Optim2: We do not work with all
 * indices but build equivalence classes and work only with the representatives.
 * (We introduce only one oldCell variable for each equivalence class) 
 * <li> Optim3: For each index i that is disjoint for the store index we do not introduce the
 * variable oldCell_i, but use aNew[i] instead. 
 * <li> Optim4: For each i∈Idx we check
 * the context if we find some term tEq that is equivalent to oldCell_i. In case
 * we found some we use tEq instead of oldCell_i. 
 * <li> Optim5: (Only sound in
 * combination with Optim3. For each pair i,k∈Idx that are both disjoint from
 * storeIndex, we can drop the "i == k ==> oldCell_i == oldCell_k" term.
 * Rationale: we use aNew[i] and aNew[k] instead of oldCell_i and oldCell_k,
 * hence the congruence information is already given implicitly.
 * </ul>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class Elim1Store {
	
	private static final Comparator<Term> FEWER_VARIABLE_FIRST = new Comparator<Term>() {

		@Override
		public int compare(final Term o1, final Term o2) {
			return o2.getFreeVars().length - o1.getFreeVars().length;
		}
	};
	private static final String AUX_VAR_NEW_ARRAY = "arrayElimArr";
	private static final String AUX_VAR_INDEX = "arrayElimIndex";
	private static final String AUX_VAR_ARRAYCELL = "arrayElimCell";

	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private static final boolean DEBUG_EXTENDED_RESULT_CHECK = false;
	private static final boolean APPLY_DOUBLE_CASE_SIMPLIFICATION = true;
	private static final boolean APPLY_RESULT_SIMPLIFICATION = false;
	private static final boolean DEBUG_CRASH_ON_LARGE_SIMPLIFICATION_POTENTIAL = false;
	
	private static final boolean SELECT_OVER_STORE_PREPROCESSING = !false;


	public Elim1Store(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final int quantifier) {
		super();
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
	}

	public EliminationTask elim1(final int quantifier, final TermVariable eliminatee, final Term inputTerm) {
		assert UltimateNormalFormUtils.respectsUltimateNormalForm(inputTerm) : "invalid input";
		final Term[] xjunctsOuter = QuantifierUtils.getXjunctsOuter(quantifier, inputTerm);
		if (xjunctsOuter.length > 1) {
			throw new AssertionError("several disjuncts! " + inputTerm);
		}
		
		if (false && SELECT_OVER_STORE_PREPROCESSING) {
			final Set<ApplicationTerm> allSelectTerms = new ApplicationTermFinder("select", false).findMatchingSubterms(inputTerm);
			for (final ApplicationTerm selectTerm : allSelectTerms) {
				final ArraySelectOverStore asos = ArraySelectOverStore.convert(selectTerm);
				if (asos != null) {
					if (asos.getArrayStore().getArray().equals(eliminatee)) {
						final Term selectIndex = asos.getIndex();
						final Term storeIndex = asos.getArrayStore().getIndex();
						Term derCase;
						{
							final Term replacement = asos.getArrayStore().getValue();
							final Map<Term, Term> substitutionMapping = Collections.singletonMap(selectTerm,
									replacement);
							final Term updated = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(inputTerm);
							final Term derTerm = QuantifierUtils.applyDerOperator(mScript, quantifier, selectIndex,
									storeIndex);
							derCase = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, derTerm, updated);
						}
						Term antiDerCase;
						{
							final Term replacement = SmtUtils.select(mScript, asos.getArrayStore().getArray(),
									selectIndex);
							final Map<Term, Term> substitutionMapping = Collections.singletonMap(selectTerm,
									replacement);
							final Term updated = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(inputTerm);
							final Term antiDerTerm = QuantifierUtils.applyAntiDerOperator(mScript, quantifier,
									selectIndex, storeIndex);
							antiDerCase = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, antiDerTerm,
									updated);
						}
						final Term simpl = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, quantifier,
								derCase, antiDerCase);
						return new EliminationTask(quantifier, Collections.singleton(eliminatee), simpl);
						// throw new AssertionError("select-over-store");
					}
				}
			}
		}


		final Set<TermVariable> newAuxVars = new LinkedHashSet<>();
		final Term preprocessedInput;

		{
			//anti-DER preprocessing
			final ArrayEqualityExplicator aadk = new ArrayEqualityExplicator(mMgdScript, eliminatee, quantifier);
			final Term antiDerPreprocessed = aadk.transform(inputTerm);
			newAuxVars.addAll(aadk.getNewAuxVars());
			final DerPreprocessor dp = new DerPreprocessor(mServices, mMgdScript, eliminatee, quantifier);
			final Term withReplacement = dp.transform(antiDerPreprocessed);
			newAuxVars.addAll(dp.getNewAuxVars());
			final Term definitions = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, dp.getAuxVarDefinitions());
			preprocessedInput = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, withReplacement, definitions);
			if (dp.introducedDerPossibility()) {
				// do DER
				final EliminationTask afterDer = ElimStorePlain.applyNonSddEliminations(mServices, mMgdScript,
						new EliminationTask(quantifier, Collections.singleton(eliminatee), preprocessedInput),
						PqeTechniques.ONLY_DER);
				newAuxVars.addAll(afterDer.getEliminatees());
				return new EliminationTask(quantifier, newAuxVars, afterDer.getTerm());
			} 

		}


		final List<ApplicationTerm> selectTerms = extractArrayReads(eliminatee, preprocessedInput);
		final Set<Term> selectIndices = new HashSet<>();
		if (SELECT_OVER_STORE_PREPROCESSING) {
			final Set<ApplicationTerm> allSelectTerms = new ApplicationTermFinder("select", false).findMatchingSubterms(preprocessedInput);
			final Map<Term, Term> substitutionMappingPre = new HashMap<>();
			for (final ApplicationTerm selectTerm : allSelectTerms) {
				final MultiDimensionalSelectOverStore mdsos = MultiDimensionalSelectOverStore.convert(selectTerm);
				if (mdsos != null) {
					if (mdsos.getStore().getArray().equals(eliminatee)) {
						final ArrayIndex selectIndex = mdsos.getSelect().getIndex();
						final ArrayIndex storeIndex = mdsos.getStore().getIndex();
						final ThreeValuedEquivalenceRelation<Term> tver = analyzeIndexEqualities(selectIndex, storeIndex, quantifier, xjunctsOuter);
						final EqualityStatus indexEquality = checkIndexEquality(selectIndex, storeIndex, tver);
						switch (indexEquality) {
						case EQUAL:
							substitutionMappingPre.put(selectTerm, mdsos.getStore().getValue());
							break;
						case NOT_EQUAL:
							final MultiDimensionalSelect mds = new MultiDimensionalSelect(mdsos.getStore().getArray(), selectIndex, mScript);
							substitutionMappingPre.put(selectTerm, mds.getSelectTerm());
							break;
						case UNKNOWN:
							// do nothing
							break;
						default:
							throw new AssertionError();
						}
					}
				}
			}
			new SubstitutionWithLocalSimplification(mMgdScript, substitutionMappingPre);
		}
		
		
		final List<ArrayStore> stores = extractStores(eliminatee, inputTerm);
//		if (stores.size() > 1) {
//			throw new AssertionError("not yet supported: multiple stores " + inputTerm);
//		}
		




		final ThreeValuedEquivalenceRelation<Term> equalityInformation = collectComplimentaryEqualityInformation(
				mMgdScript.getScript(), quantifier, preprocessedInput, selectTerms, stores);
		if (equalityInformation == null) {
			final Term absobingElement = QuantifierUtils.getNeutralElement(mScript, quantifier);
			mLogger.warn("Array PQE input equivalent to " + absobingElement);
			return new EliminationTask(quantifier, Collections.emptySet(), absobingElement);
		}
		

		for (final ApplicationTerm selectTerm : selectTerms) {
			final Term selectIndex = getIndexOfSelect(selectTerm);
			selectIndices.add(selectIndex);
		}

		final Pair<ThreeValuedEquivalenceRelation<Term>, List<Term>> analysisResult =
				analyzeIndexEqualities(quantifier, selectIndices, stores, preprocessedInput, equalityInformation, eliminatee);
		if (analysisResult == null) {
			final Term absobingElement = QuantifierUtils.getNeutralElement(mScript, quantifier);
			mLogger.warn("Array PQE input equivalent to " + absobingElement);
			return new EliminationTask(quantifier, Collections.emptySet(), absobingElement);
		}

		final List<Term> selectIndexRepresentatives = new ArrayList<>();
		final List<Term> allIndexRepresentatives = new ArrayList<>();
		for (final Term selectIndex : selectIndices) {
			final Term selectIndexRepresentative = equalityInformation.getRepresentative(selectIndex);
			selectIndexRepresentatives.add(selectIndexRepresentative);
			allIndexRepresentatives.add(selectIndexRepresentative);
			// following is needed because we may now construct 
			// a[selectIndexRepresentative] instead of
			// a[selectIndex]
			final Term oldSelect = constructOldSelectTerm(mMgdScript, eliminatee, selectIndex);
			final Term oldSelectForRep = constructOldSelectTerm(mMgdScript, eliminatee, selectIndexRepresentative);
			equalityInformation.addElement(oldSelectForRep);
			equalityInformation.reportEquality(oldSelectForRep, oldSelect);
		}
		final List<Term> storeIndexRepresentatives = new ArrayList<>();
		for (final ArrayStore store : stores) {
			final Term storeIndexRepresentative = equalityInformation.getRepresentative(store.getIndex());
			storeIndexRepresentatives.add(storeIndexRepresentative);
			allIndexRepresentatives.add(storeIndexRepresentative);
		}
//		Term storeIndexRepresentative;
//		if (storeIndex == null) {
//			storeIndexRepresentative = null;
//		} else {
//			storeIndexRepresentative = equalityInformation.getRepresentative(storeIndex);
//			allIndexRepresentatives.add(storeIndexRepresentative);
//		}

		final Set<Term> allIndices = new HashSet<>(selectIndices);
		for (final ArrayStore store : stores) {
			allIndices.add(store.getIndex());
		}
//		if (storeIndex != null) {
//			allIndices.add(storeIndex);
//		}
		final ThreeValuedEquivalenceRelation<Term> indexEqualityInformation = analysisResult.getFirst().projectTo(allIndices);
		final Term indexEqualityInformationTerm = equivalencesToTerm(mScript, indexEqualityInformation, quantifier);


		final AuxVarConstructor auxVarConstructor = new AuxVarConstructor();
		final IndexMappingProvider imp = new IndexMappingProvider(allIndexRepresentatives, eliminatee, equalityInformation,
				auxVarConstructor, quantifier);

		final Map<Term, Term> indexMapping = imp.getIndexReplacementMapping();
		final List<Term> indexMappingDefinitions = imp.getIndexMappingDefinitions();

		final Term equalitiesDetectedBySolver = QuantifierUtils.applyDualFiniteConnective(mScript,
				quantifier, analysisResult.getSecond());
		final Term indexDefinitionsTerm =
				QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, indexMappingDefinitions);
		final Term intermediateTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
				indexDefinitionsTerm, preprocessedInput, equalitiesDetectedBySolver, indexEqualityInformationTerm);

		final Map<ArrayStore, Term> newArrayMapping = new HashMap<>();
		for (final ArrayStore store : stores) {
			final Term newArray;
			final EqProvider eqProvider = new EqProvider(preprocessedInput, eliminatee, quantifier);
			final Term eqArray = eqProvider.getEqTerm(store.toTerm(mScript));
			if (eqArray != null) {
				newArray = eqArray;
			} else {
				newArray = auxVarConstructor.constructAuxVar(AUX_VAR_NEW_ARRAY, eliminatee.getSort());
			}
			newArrayMapping.put(store, newArray);
		}
		
//		final Term newArray;
//		{
//			if (storeIndex == null) {
//				newArray = null;
//			} else {
//				final EqProvider eqProvider = new EqProvider(preprocessedInput, eliminatee, quantifier);
//				final Term eqArray = eqProvider.getEqTerm(storeTerm);
//				if (eqArray != null) {
//					newArray = eqArray;
//				} else {
//					newArray = auxVarConstructor.constructAuxVar(AUX_VAR_NEW_ARRAY, eliminatee.getSort());
//				}
//			}
//		}

		final Map<Term, Term> oldCellMapping = constructOldCellValueMapping(selectIndexRepresentatives, newArrayMapping,
				equalityInformation, indexMapping, auxVarConstructor, eliminatee, quantifier);
		newAuxVars.addAll(auxVarConstructor.getConstructedAuxVars());


		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<ArrayStore, Term> entry : newArrayMapping.entrySet()) {
			substitutionMapping.put(entry.getKey().toTerm(mScript), entry.getValue());
		}
		for (final Term selectIndex : selectIndices) {
			final Term oldSelect = constructOldSelectTerm(mMgdScript, eliminatee, selectIndex);
			final Term indexRepresentative = equalityInformation.getRepresentative(selectIndex);
			if (oldCellMapping.containsKey(indexRepresentative)) {
				substitutionMapping.put(oldSelect, oldCellMapping.get(indexRepresentative));
			} else {
				throw new AssertionError("should be dead code by now");
//				final Term newSelect = mMgdScript.getScript().term("select", newArray, indexRepresentative);
//				substitutionMapping.put(oldSelect, newSelect);
			}
		}

		final List<Term> singleCaseJuncts = new ArrayList<>();
		final List<Term> doubleCaseJuncts = new ArrayList<>();

		
		final Pair<List<Term>, List<Term>> wc = constructWriteConstraints((ArrayList<Term>) selectIndexRepresentatives, equalityInformation,
					mMgdScript, indexMapping, oldCellMapping, eliminatee, quantifier, newArrayMapping, substitutionMapping);
		singleCaseJuncts.addAll(wc.getFirst());
		doubleCaseJuncts.addAll(wc.getSecond());


		final Pair<List<Term>, List<Term>> cc = constructIndexValueConnection(
				(ArrayList<Term>) selectIndexRepresentatives, equalityInformation, mMgdScript, indexMapping,
				oldCellMapping, eliminatee, quantifier);
		singleCaseJuncts.addAll(cc.getFirst());
		doubleCaseJuncts.addAll(cc.getSecond());


				
		final Term singleCaseTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, singleCaseJuncts);

		final Term transformedTerm =
				new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(intermediateTerm);
		final Term storedValueInformation = constructStoredValueInformation(quantifier, eliminatee, newArrayMapping, indexMapping, substitutionMapping, equalityInformation);
		Term result = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
				transformedTerm, storedValueInformation, singleCaseTerm);
		if (!doubleCaseJuncts.isEmpty()) {
			final Term doubleCaseTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, doubleCaseJuncts);
			final Term doubleCaseTermMod; 
			if (APPLY_DOUBLE_CASE_SIMPLIFICATION) {
				final boolean contextIsDisjunctive = (quantifier == QuantifiedFormula.FORALL);
				doubleCaseTermMod = new SimplifyDDAWithTimeout(mScript, false, mServices, result, contextIsDisjunctive)
						.getSimplifiedTerm(doubleCaseTerm);
			} else {
				doubleCaseTermMod = doubleCaseTerm;
			}
			result = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, result, doubleCaseTermMod);
		}
		assert !Arrays.asList(result.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee
		+ " term size " + new DagSizePrinter(result);
		{
			final StringBuilder sb = new StringBuilder();
			sb.append("Elim1");
			if (inputTerm == preprocessedInput) {
				sb.append(" did not use preprocessing");
			} else {
				sb.append(" applied some preprocessing");
			}
			final int dim = new MultiDimensionalSort(eliminatee.getSort()).getDimension();
			sb.append(" eliminated variable of array dimension " + dim);
			sb.append(", " + stores.size() + " stores");
			sb.append(", " + selectIndices.size() + " select indices");
			sb.append(", " + selectIndexRepresentatives.size() + " select index equivalence classes");
			final int indexPairs = (selectIndexRepresentatives.size() * selectIndexRepresentatives.size()
					- selectIndexRepresentatives.size()) / 2;
			sb.append(String.format(", %d disjoint index pairs (out of %d index pairs)",
					equalityInformation.getDisequalities().size(), indexPairs));
			sb.append(String.format(", introduced %d new quantified variables", newAuxVars.size()));
			sb.append(String.format(", introduced %d case distinctions", doubleCaseJuncts.size()));
			sb.append(String.format(", treesize of input %d treesize of output %d",
					new DAGSize().treesize(inputTerm), new DAGSize().treesize(result)));
			mLogger.info(sb.toString());
		}
		final EliminationTask resultEt;
		if (APPLY_RESULT_SIMPLIFICATION) {
			if (DEBUG_CRASH_ON_LARGE_SIMPLIFICATION_POTENTIAL) {
				final ExtendedSimplificationResult esrQuick = SmtUtils.simplifyWithStatistics(mMgdScript, result, mServices, SimplificationTechnique.SIMPLIFY_QUICK);
				mLogger.info(String.format("quick treesize reduction %d that is %2.1f percent of original size",
						esrQuick.getReductionOfTreeSize(), esrQuick.getReductionRatioInPercent()));
				if (esrQuick.getReductionRatioInPercent() < 70) {
					throw new AssertionError("Reduction: " + esrQuick.getReductionRatioInPercent() + " Input: " + preprocessedInput);
				}
			}
			final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mMgdScript, result, mServices, SimplificationTechnique.SIMPLIFY_DDA);
			final Term simplified = esr.getSimplifiedTerm();
			final String sizeMessage = String.format("treesize reduction %d that is %2.1f percent of original size",
					esr.getReductionOfTreeSize(), esr.getReductionRatioInPercent());
			if (esr.getReductionRatioInPercent() <= 70) {
				mLogger.info(sizeMessage);				
			} else {
				mLogger.info(sizeMessage);
			}
			mLogger.info("treesize after simplification " + new DAGSize().treesize(simplified));
			resultEt = new EliminationTask(quantifier, newAuxVars, simplified);
		} else {
			resultEt = new EliminationTask(quantifier, newAuxVars, result);
		}
		assert !DEBUG_EXTENDED_RESULT_CHECK  || EliminationTask.areDistinct(mMgdScript.getScript(), resultEt, new EliminationTask(quantifier,
				Collections.singleton(eliminatee), inputTerm)) != LBool.SAT : "Bug array QE Input: " + inputTerm
						+ " Result:" + resultEt;
		return resultEt;

	}
	
	
	private EqualityStatus checkIndexEquality(final ArrayIndex selectIndex, final ArrayIndex storeIndex,
			final ThreeValuedEquivalenceRelation<Term> tver) {
		for (int i=0; i<selectIndex.size(); i++) {
			final EqualityStatus eqStaus = tver.getEqualityStatus(selectIndex.get(i), storeIndex.get(i));
			if (eqStaus == EqualityStatus.NOT_EQUAL || eqStaus == EqualityStatus.UNKNOWN) {
				return eqStaus;
			}
		}
		return EqualityStatus.EQUAL;
	}

	private ThreeValuedEquivalenceRelation<Term> analyzeIndexEqualities(final ArrayIndex selectIndex, final ArrayIndex storeIndex, final int quantifier, final Term[] context) {
		final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<>();
		for (final Term term : selectIndex) {
			addComplimentaryEqualityInformation(mScript, quantifier, context, term, tver);
		}
		for (final Term term : storeIndex) {
			addComplimentaryEqualityInformation(mScript, quantifier, context, term, tver);
		}
		return tver;
	}

	private Term equivalencesToTerm(final Script script, final ThreeValuedEquivalenceRelation<Term> tver, final int quantifier) {

		final List<Term> elementEqualities = tver.getSupportingEqualities().entrySet().stream()
				.map(en -> QuantifierUtils.applyDerOperator(script, quantifier, en.getKey(), en.getValue()))
				.collect(Collectors.toList());
		final List<Term> elementDisequalities = tver.getDisequalities().entrySet().stream()
				.map(pair -> QuantifierUtils.applyAntiDerOperator(script, quantifier, pair.getKey(), pair.getValue()))
				.collect(Collectors.toList());

		final List<Term> result = new ArrayList<>(elementEqualities.size() + elementDisequalities.size());
		result.addAll(elementEqualities);
		result.addAll(elementDisequalities);
		return QuantifierUtils.applyDualFiniteConnective(script, quantifier, result);
	}

	/**
	 * Let eliminatee be the array that is eliminated and (select eliminatee idx
	 * v) a select term. Construct mapping that assigns the select term an
	 * auxiliary variable the represents this array cell. If we know that the
	 * index of the store that we currently process is disjoint from idx, we do
	 * not add the auxiliary variable (the new cell will have same value as old
	 * cell). As an optimization, we only construct one auxiliary variable for
	 * each equivalence class of indices.
	 * @param newAuxArray
	 * @param auxVarConstructor
	 * @param eliminatee
	 * @param quantifier
	 */
	private Map<Term, Term> constructOldCellValueMapping(final List<Term> selectIndexRepresentatives,
			final Map<ArrayStore, Term> newArrayMapping, final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final Map<Term, Term> rawIndex2replacedIndex,
			final AuxVarConstructor auxVarConstructor, final TermVariable eliminatee,
			final int quantifier) {
		final Sort valueSort = eliminatee.getSort().getArguments()[1];
		final IValueConstruction<Term, TermVariable> valueConstruction = new IValueConstruction<Term, TermVariable>() {

			@Override
			public TermVariable constructValue(final Term index) {
				final TermVariable oldCell = auxVarConstructor.constructAuxVar(AUX_VAR_ARRAYCELL, valueSort);
				return oldCell;
			}

		};
		final ConstructionCache<Term, TermVariable> cc = new ConstructionCache<>(valueConstruction);
		final Map<Term, Term> oldCellMapping = new HashMap<>();
		for (final Term selectIndexRepresentative : selectIndexRepresentatives) {
			Term oldCellValue;
			final Term oldValueInNewArray = getOldValueInNewArray(newArrayMapping, equalityInformation, rawIndex2replacedIndex, selectIndexRepresentative);
			if (oldValueInNewArray != null) {
				oldCellValue = oldValueInNewArray;
			} else {
				oldCellValue = constructOldCellValue(equalityInformation, eliminatee, cc, selectIndexRepresentative);
			}
			oldCellMapping.put(selectIndexRepresentative, oldCellValue);
		}
		return oldCellMapping;
	}

	private Term getOldValueInNewArray(final Map<ArrayStore, Term> newAuxArrayMapping,
			final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final Map<Term, Term> rawIndex2replacedIndex, final Term selectIndexRepresentative) {
		for (final Entry<ArrayStore, Term> entry : newAuxArrayMapping.entrySet()) {
			final Term storeIndex = entry.getKey().getIndex();
			if (equalityInformation.getEqualityStatus(selectIndexRepresentative,
					storeIndex) == EqualityStatus.NOT_EQUAL) {
				final Term replacementSelectIndex = rawIndex2replacedIndex.get(selectIndexRepresentative);
				final Term newAuxArray = entry.getValue();
				final Term newSelect = mMgdScript.getScript().term("select", newAuxArray, replacementSelectIndex);
				return newSelect;
//						oldCellMapping.put(selectIndexRepresentative, newSelect);
				
			}
		}
		return null;
	}

	private Term constructOldCellValue(final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final TermVariable eliminatee, final ConstructionCache<Term, TermVariable> cc,
			final Term selectIndexRepresentative) {
		Term oldCellValue;
		{
			final Term oldSelect = constructOldSelectTerm(mMgdScript, eliminatee, selectIndexRepresentative);
			final Term oldSelectRepresentative = equalityInformation.getRepresentative(oldSelect);
			final Term eqTerm = findNiceReplacementForRepresentative(oldSelectRepresentative, eliminatee, equalityInformation);
			if (eqTerm != null) {
				oldCellValue = eqTerm;
			} else {
				final TermVariable oldCellVariable = cc.getOrConstruct(selectIndexRepresentative);
				oldCellValue = oldCellVariable;
			}
		}
		return oldCellValue;
	}
		
		
		private void checkEqualityStatus(final int mQuantifier, final ThreeValuedEquivalenceRelation<Term> tver,
			final List<Term> relationsDetectedViaSolver, final IncrementalPlicationChecker iea, final Term index1,
			final Term index2) throws AssertionError {
		final Term eq = SmtUtils.binaryEquality(mScript, index1, index2);
		if (SmtUtils.isTrue(eq)) {
			tver.reportEquality(index1, index2);
			assert !tver.isInconsistent() : "inconsistent equality information";
		} else if (SmtUtils.isFalse(eq)) {
			tver.reportDisequality(index1, index2);
			assert !tver.isInconsistent() : "inconsistent equality information";
		} else {
			final Term neq = SmtUtils.not(mScript, eq);
			final Validity isEqual = iea.checkPlication(eq);
			if (isEqual == Validity.UNKNOWN && mLogger.isWarnEnabled()) {
				mLogger.warn("solver failed to check if following equality is implied: " + eq);
			}
			if (isEqual == Validity.VALID) {
				if (mQuantifier == QuantifiedFormula.EXISTS) {
					tver.reportEquality(index1, index2);
					assert !tver.isInconsistent() : "inconsistent equality information";
				} else if (mQuantifier == QuantifiedFormula.FORALL) {
					tver.reportDisequality(index1, index2);
					assert !tver.isInconsistent() : "inconsistent equality information";
				} else {
					throw new AssertionError("unknown quantifier");
				}
				relationsDetectedViaSolver.add(eq);
				mLogger.info("detected equality via solver");
			} else {
				final Validity notEqualsHolds = iea.checkPlication(neq);
				if (notEqualsHolds == Validity.UNKNOWN && mLogger.isWarnEnabled()) {
					mLogger.warn("solver failed to check if following not equals relation is implied: "
							+ eq);
				}
	
				if (notEqualsHolds == Validity.VALID) {
					if (mQuantifier == QuantifiedFormula.EXISTS) {
						tver.reportDisequality(index1, index2);
						assert !tver.isInconsistent() : "inconsistent equality information";
					} else if (mQuantifier == QuantifiedFormula.FORALL) {
						tver.reportEquality(index1, index2);
						assert !tver.isInconsistent() : "inconsistent equality information";
					} else {
						throw new AssertionError("unknown quantifier");
					}
					mLogger.info("detected not equals via solver");
					relationsDetectedViaSolver.add(neq);
				}
			}
		}
	}


		private Pair<ThreeValuedEquivalenceRelation<Term>, List<Term>> analyzeIndexEqualities(final int mQuantifier,
				final Set<Term> selectIndices, final List<ArrayStore> stores, final Term preprocessedInput, final ThreeValuedEquivalenceRelation<Term> tver, final TermVariable eliminatee) {
		
			mScript.echo(new QuotedObject("starting to analyze index equalities"));
			final List<Term> relationsDetectedViaSolver = new ArrayList<>();
			final ArrayList<Term> allIndicesList = new ArrayList<>(selectIndices);
			for (final ArrayStore store : stores) {
				allIndicesList.add(store.getIndex());
			}
			final Plication plication;
			if (mQuantifier == QuantifiedFormula.EXISTS) {
				plication = Plication.IMPLICATION;
			} else if (mQuantifier == QuantifiedFormula.FORALL) {
				plication = Plication.EXPLICATION;
			} else {
				throw new AssertionError("unknown quantifier");
			}
			final IncrementalPlicationChecker iea = new IncrementalPlicationChecker(plication, mMgdScript, preprocessedInput);
			final Term absorbingElement = QuantifierUtils.getNeutralElement(mScript, mQuantifier);
			final Validity validity = iea.checkPlication(absorbingElement);
			if (validity == Validity.VALID) {
				iea.unlockSolver();
				return null;
			}
			
			final List<Term> allValues = new ArrayList<>();
			final Map<Term, Term> value2selectIndex = new HashMap<>();
			final Map<Term, Term> selectIndex2value = new HashMap<>();
			for (final Term selectIndex : selectIndices) {
				final Term oldSelect = constructOldSelectTerm(mMgdScript, eliminatee, selectIndex);
				allValues.add(oldSelect);
				value2selectIndex.put(oldSelect, selectIndex);
				selectIndex2value.put(selectIndex, oldSelect);
			}
			for (final ArrayStore arrayStore : stores) {
				allValues.add(arrayStore.getValue());
			}
			cheapAndSimpleIndexValueAnalysis(allIndicesList, selectIndex2value, allValues, value2selectIndex, tver);
			
			
			for (int i = 0; i < allIndicesList.size(); i++) {
				for (int j = i + 1; j < allIndicesList.size(); j++) {
					//TODO: try to obtain equal term with few variables
					final Term index1 = allIndicesList.get(i);
					final Term index2 = allIndicesList.get(j);
					if (tver.getEqualityStatus(index1, index2) != EqualityStatus.UNKNOWN) {
						// result already known we do not have to check
						continue;
						// TODO: for some the solver result might have been unknown
						// we should avoid to these are checked again
					}
					checkEqualityStatus(mQuantifier, tver, relationsDetectedViaSolver, iea, index1, index2);
				}
			}

			cheapAndSimpleIndexValueAnalysis(allIndicesList, selectIndex2value, allValues, value2selectIndex, tver);
			for (int i = 0; i < allValues.size(); i++) {
				for (int j = i + 1; j < allValues.size(); j++) {
					final Term value1 = allValues.get(i);
					final Term value2 = allValues.get(j);
					if (tver.getEqualityStatus(value1, value2) != EqualityStatus.UNKNOWN) {
						// result already known we do not have to check
						continue;
						// TODO: for some the solver result might have been unknown
						// we should avoid to these are checked again
					}
					checkEqualityStatus(mQuantifier, tver, relationsDetectedViaSolver, iea, value1, value2);
				}
			}
			
			
			iea.unlockSolver();
			mScript.echo(new QuotedObject("finished analysis of index equalities"));
			return new Pair<>(tver, relationsDetectedViaSolver);
		}





		private void cheapAndSimpleIndexValueAnalysis(final ArrayList<Term> allIndicesList, final Map<Term, Term> selectIndex2value,
				final List<Term> allValues, final Map<Term, Term> value2selectIndex, final ThreeValuedEquivalenceRelation<Term> tver) {
			final LocalSimplificationsEqualityChecker lsec = new LocalSimplificationsEqualityChecker();
			for (int i = 0; i < allIndicesList.size(); i++) {
				for (int j = i + 1; j < allIndicesList.size(); j++) {
					final Term index1 = allIndicesList.get(i);
					final Term index2 = allIndicesList.get(j);
					EqualityStatus eq = tver.getEqualityStatus(index1, index2);
					if (eq == EqualityStatus.UNKNOWN) {
						eq = lsec.checkEquality(index1, index2);
						if (eq == EqualityStatus.EQUAL) {
							tver.reportEquality(index1, index2);
						} else if (eq == EqualityStatus.NOT_EQUAL) { 
							tver.reportDisequality(index1, index2);
						}
					}
					if (eq == EqualityStatus.EQUAL) {
						final Term oldSelect1 = selectIndex2value.get(index1);
						final Term oldSelect2 = selectIndex2value.get(index2);
						if (oldSelect1 != null && oldSelect2 != null) {
							tver.reportEquality(oldSelect1, oldSelect2);
						}
					}
				}
			}
			for (int i = 0; i < allValues.size(); i++) {
				for (int j = i + 1; j < allValues.size(); j++) {
					final Term value1 = allValues.get(i);
					final Term value2 = allValues.get(j);
					EqualityStatus eq = tver.getEqualityStatus(value1, value2);
					if (eq == EqualityStatus.UNKNOWN) {
						eq = lsec.checkEquality(value1, value2);
						if (eq == EqualityStatus.EQUAL) {
							tver.reportEquality(value1, value2);
						} else if (eq == EqualityStatus.NOT_EQUAL) { 
							tver.reportDisequality(value1, value2);
						}
					}
					if (eq == EqualityStatus.NOT_EQUAL) {
						final Term index1 = value2selectIndex.get(value1);
						final Term index2 = value2selectIndex.get(value2);
						if (index1 != null && index2 != null) {
							tver.reportDisequality(index1, index2);
						}
					}
				}
			}
		}

		private Term getIndexOfSelect(final ApplicationTerm appTerm) {
			assert (appTerm.getParameters().length == 2) : "no select";
			assert (appTerm.getFunction().getName().equals("select")) : "no select";
			return appTerm.getParameters()[1];
		}


		/**
		 * Add equality information for term that are obtained from context by
		 * only looking at (dis)eqality terms.
		 * @return 
		 * @return true if an inconsitency was detected 
		 */
	private static boolean addComplimentaryEqualityInformation(final Script script, final int quantifier,
			final Term[] context, final Term term, final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
			equalityInformation.addElement(term);
			final Pair<Set<Term>, Set<Term>> indexEqual = EqualityInformation.getEqTerms(script, term, context, null);
			Set<Term> derTerms;
			Set<Term> antiDerTerms;
			if (quantifier == QuantifiedFormula.EXISTS) {
				derTerms = indexEqual.getFirst();
				antiDerTerms = indexEqual.getSecond();
			} else if (quantifier == QuantifiedFormula.FORALL) {
				derTerms = indexEqual.getSecond();
				antiDerTerms = indexEqual.getFirst();
			} else {
				throw new AssertionError("unknown quantifier");
			}
			for (final Term equal : derTerms) {
				equalityInformation.addElement(equal);
				equalityInformation.reportEquality(term, equal);
				if (equalityInformation.isInconsistent()) {
					return true;
				}
			}
			for (final Term disequal : antiDerTerms) {
				equalityInformation.addElement(disequal);
				equalityInformation.reportDisequality(term, disequal);
				if (equalityInformation.isInconsistent()) {
					return true;
				}
			}
			return false;
		}


		private ThreeValuedEquivalenceRelation<Term> collectComplimentaryEqualityInformation(final Script script, final int quantifier,
				final Term preprocessedInput, final List<ApplicationTerm> selectTerms, final List<ArrayStore> stores) {
			final ThreeValuedEquivalenceRelation<Term> equalityInformation = new ThreeValuedEquivalenceRelation<>();
			final Term[] context = QuantifierUtils.getXjunctsInner(quantifier, preprocessedInput);
			boolean inconsistencyDetected = false;
			for (final ApplicationTerm selectTerm : selectTerms) {
				final Term selectIndex = getIndexOfSelect(selectTerm);
				inconsistencyDetected |= addComplimentaryEqualityInformation(script, quantifier, context, selectIndex, equalityInformation);
				if (inconsistencyDetected) {
					return null;
				}
				inconsistencyDetected |= addComplimentaryEqualityInformation(script, quantifier, context, selectTerm, equalityInformation);
				if (inconsistencyDetected) {
					return null;
				}

			}
			for (final ArrayStore arrayStore : stores) {
				inconsistencyDetected |= addComplimentaryEqualityInformation(script, quantifier, context, arrayStore.getIndex(), equalityInformation);
				if (inconsistencyDetected) {
					return null;
				}

				inconsistencyDetected |= addComplimentaryEqualityInformation(script, quantifier, context, arrayStore.getValue(), equalityInformation);
				if (inconsistencyDetected) {
					return null;
				}
			}
			return equalityInformation;
		}


	private Term constructStoredValueInformation(final int quantifier, final TermVariable eliminatee,
			final Map<ArrayStore, Term> newArrayMapping, final Map<Term, Term> indexMapping,
			final Map<Term, Term> substitutionMapping, final ThreeValuedEquivalenceRelation<Term> equalityInformation) throws AssertionError {
		final List<Term> storedValueInformation = new ArrayList<>();
		for (final Entry<ArrayStore, Term> entry : newArrayMapping.entrySet()) {
			final Term indexRepresentative = equalityInformation.getRepresentative(entry.getKey().getIndex());
			final Term replacementIndex = indexMapping.get(indexRepresentative);
			storedValueInformation.add(QuantifierUtils.applyDerOperator(mMgdScript.getScript(), quantifier,
					mScript.term("select", entry.getValue(), replacementIndex),
					new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping)
							.transform(entry.getKey().getValue())));
		}
		return QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, storedValueInformation);
	}

		private static List<ApplicationTerm> extractArrayReads(final TermVariable eliminatee, final Term term) {
			final List<ApplicationTerm> result = new ArrayList<>();
			final Set<ApplicationTerm> selectTerms = new ApplicationTermFinder("select", false).findMatchingSubterms(term);
			for (final ApplicationTerm selectTerm : selectTerms) {
				if (selectTerm.getParameters()[0].equals(eliminatee)) {
					result.add(selectTerm);
				}
			}
			return result;
		}
		
		private List<ArrayStore> extractStores(final TermVariable eliminatee, final Term term) {
			final List<ArrayStore> result = new ArrayList<>();
			final Set<ApplicationTerm> stores = new ApplicationTermFinder("store", false).findMatchingSubterms(term);
			for (final ApplicationTerm appTerm : stores) {
				if (appTerm.getParameters()[0].equals(eliminatee)) {
					result.add(new ArrayStore(appTerm));
				}
			}
			return result;
		}

		private static boolean occursIn(final TermVariable tv, final Term term) {
			return Arrays.asList(term.getFreeVars()).contains(tv);
		}

		/**
		 * <ul>
		 * <li> ∀k∈Idx. i == k ==> oldCell_i == oldCell_k) 
		 * <li> (i != storeIndex) ==> (aNew[i] == oldCell_i)
		 * </ul>
		 */
		private static Pair<List<Term>, List<Term>> constructIndexValueConnection(final ArrayList<Term> selectIndices,
				final ThreeValuedEquivalenceRelation<Term> indexEqualityInformation, final ManagedScript mgdScript,
				final Map<Term, Term> representative2replacement, final Map<Term, ? extends Term> index2value,
				final TermVariable eliminatee, final int quantifier) {
			final List<Term> resultConjuncts1case = new ArrayList<Term>();
			final List<Term> resultConjuncts2cases = new ArrayList<Term>();
			for (int i = 0; i < selectIndices.size(); i++) {
				for (int j = i+1; j < selectIndices.size(); j++) {
					if (!indexEqualityInformation.isRepresentative(selectIndices.get(j))) {
						throw new AssertionError("representatives only");
					}
					final Term index1 = selectIndices.get(i);
					final Term index2 = selectIndices.get(j);
					if (selectTermsWithsimilarArray(index2value.get(index1), index2value.get(index2))) {
						// Both old values are represented by a select on a 
						// similar array (some new aux array).
						// We omit this conjunct because the congruence
						// information is already provided by the array theory.
						continue;
					}
		
					final Term indexEqualityTerm;
					final EqualityStatus eqStatus = indexEqualityInformation.getEqualityStatus(index1, index2);
					switch (eqStatus) {
					case EQUAL:
						indexEqualityTerm = null;
						break;
					case NOT_EQUAL:
						// junct can be omitted
						continue;
					case UNKNOWN:
						final Term replacementIndex1 = representative2replacement.get(index1);
						assert !occursIn(eliminatee, replacementIndex1) : "var is still there";
						final Term replacementIndex2 = representative2replacement.get(index2);
						assert !occursIn(eliminatee, replacementIndex2) : "var is still there";
						indexEqualityTerm = QuantifierUtils.applyDerOperator(mgdScript.getScript(), quantifier, replacementIndex1,
								replacementIndex2);
						break;
					default:
						throw new AssertionError();
					}
					
					final Term valueEqualityTerm;
					final Term oldSelect1 = constructOldSelectTerm(mgdScript, eliminatee, index1);
					final Term oldSelect2 = constructOldSelectTerm(mgdScript, eliminatee, index2);
					final EqualityStatus valueEqualityStatus = indexEqualityInformation.getEqualityStatus(oldSelect1, oldSelect2);
					switch (valueEqualityStatus) {
					case EQUAL:
						// junct can be omitted
						continue;
					case NOT_EQUAL:
						if (indexEqualityTerm != null) {
							resultConjuncts1case.add(SmtUtils.not(mgdScript.getScript(), indexEqualityTerm));
							continue;
						} else {
							throw new AssertionError("input was inconsistent");							
						}
					case UNKNOWN:
					{
						final Term value1 = index2value.get(index1);
						assert !occursIn(eliminatee, value1) : "var is still there";
						final Term value2 = index2value.get(index2);
						assert !occursIn(eliminatee, value2) : "var is still there";
						valueEqualityTerm = QuantifierUtils.applyDerOperator(mgdScript.getScript(), quantifier, value1, value2);
					}
						break;
					default:
						throw new AssertionError();
					
					}
					final Term implication;
					if (quantifier == QuantifiedFormula.EXISTS) {
						implication = SmtUtils.or(mgdScript.getScript(),
								SmtUtils.not(mgdScript.getScript(), indexEqualityTerm), valueEqualityTerm);
					} else if (quantifier == QuantifiedFormula.FORALL) {
						implication = SmtUtils.and(mgdScript.getScript(),
								SmtUtils.not(mgdScript.getScript(), indexEqualityTerm), valueEqualityTerm);
					} else {
						throw new AssertionError("unknown quantifier");
					}
					resultConjuncts2cases.add(implication);
				}
			}
			return new Pair<List<Term>, List<Term>>(resultConjuncts1case, resultConjuncts2cases);
		}
		
		private static boolean selectTermsWithsimilarArray(final Term term1, final Term term2) {
			final ArraySelect select1 = ArraySelect.convert(term1);
			if (select1 == null) {
				return false;
			} else {
				final ArraySelect select2 = ArraySelect.convert(term2);
				if (select2 == null) {
					return false;
				} else {
					return select1.getArray() == select2.getArray();
				}	
			}
		}

		/**
		 * <ul>
		 * <li> (i == storeIndex)==> (aNew[i] == newValue) 
		 * <li> (i != storeIndex) ==> (aNew[i] == oldCell_i)
		 * </ul>
		 */
		private static Pair<List<Term>, List<Term>> constructWriteConstraints(final ArrayList<Term> selectIndexRepresentatives,
				final ThreeValuedEquivalenceRelation<Term> equalityInformation, final ManagedScript mgdScript,
				final Map<Term, Term> rawIndex2replacedIndex, final Map<Term, ? extends Term> index2value,
				final TermVariable eliminatee, final int quantifier, final Map<ArrayStore, Term> store2newArray, final Map<Term, Term> substitutionMapping) {
			final List<Term> resultConjuncts1case = new ArrayList<Term>();
			final List<Term> resultConjuncts2cases = new ArrayList<Term>();
			for(final Entry<ArrayStore, Term> entry : store2newArray.entrySet()) {
				Term storeIndexRepresentative;
				{
					final Term storeIndex = entry.getKey().getIndex();
					storeIndexRepresentative = equalityInformation.getRepresentative(storeIndex);
				}
				final Term storeValue = entry.getKey().getValue();
				final Term newAuxArray = entry.getValue();
				for (final Term selectIndexRepresentative : selectIndexRepresentatives) {
					assert equalityInformation.isRepresentative(selectIndexRepresentative) : "no representative: " + selectIndexRepresentative;
					final Term replacementStoreIndex = rawIndex2replacedIndex.get(storeIndexRepresentative);
					assert !occursIn(eliminatee, replacementStoreIndex) : "var is still there";
					final Term replacementSelectIndex = rawIndex2replacedIndex.get(selectIndexRepresentative);
					assert !occursIn(eliminatee, replacementSelectIndex) : "var is still there";
					final Term indexEquality = QuantifierUtils.applyDerOperator(mgdScript.getScript(),
							quantifier, replacementStoreIndex, replacementSelectIndex);
					final Term newSelect = mgdScript.getScript().term("select", newAuxArray, replacementSelectIndex);
					final Term storeValueReplacement = new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(storeValue);
					final Term newValueInCell = QuantifierUtils.applyDerOperator(mgdScript.getScript(),
							quantifier, newSelect, storeValueReplacement);
					final EqualityStatus indexEqStatus = equalityInformation.getEqualityStatus(storeIndexRepresentative, selectIndexRepresentative);
					switch (indexEqStatus) {
					case EQUAL:
						// this means not equal for univeral quantification
						resultConjuncts1case.add(newValueInCell);
						continue;
					case NOT_EQUAL:
						// case handled via substitution
						continue;
					case UNKNOWN: {
						final Term oldSelect = constructOldSelectTerm(mgdScript, eliminatee, selectIndexRepresentative);
						if (equalityInformation.getEqualityStatus(oldSelect, storeValue) == EqualityStatus.EQUAL) {
							resultConjuncts1case.add(newValueInCell);
							continue;
						}

						final Term succedent = newValueInCell;
						final Term negatedAntecedent = SmtUtils.not(mgdScript.getScript(), indexEquality);
						final Term positiveCase = QuantifierUtils.applyCorrespondingFiniteConnective(mgdScript.getScript(),
								quantifier, negatedAntecedent, succedent);
						resultConjuncts2cases.add(positiveCase);
					}
					{
						final Term oldCellValue = index2value.get(selectIndexRepresentative);
						final Term oldValueInCell = QuantifierUtils.applyDerOperator(mgdScript.getScript(),
								quantifier, newSelect, oldCellValue);
						final Term negatedAntecedent = indexEquality;
						final Term negativeCase = QuantifierUtils.applyCorrespondingFiniteConnective(mgdScript.getScript(),
								quantifier, negatedAntecedent, oldValueInCell);
						resultConjuncts2cases.add(negativeCase);
						break;
					}
					default:
						throw new AssertionError();
					}
				}
			}
			return new Pair<List<Term>, List<Term>>(resultConjuncts1case, resultConjuncts2cases);
}

//		private static Pair<List<Term>, List<Term>> constructWriteConstraints(final ArrayList<Term> selectIndexRepresentatives,
//				final ThreeValuedEquivalenceRelation<Term> equalityInformation, final ManagedScript mgdScript,
//				final Map<Term, Term> rawIndex2replacedIndex, final Map<Term, Pair<Term, Boolean>> oldCellMapping,
//				final TermVariable eliminatee, final int quantifier, final Map<ArrayStore, Term> newArrayMapping, final Map<Term, Term> substitutionMapping) {
//			final List<Term> resultConjuncts1case = new ArrayList<Term>();
//			final List<Term> resultConjuncts2cases = new ArrayList<Term>();
//			for (final Entry<ArrayStore, Term> store2NewArray : newArrayMapping.entrySet()) {
//				for (final Term selectIndexRepresentative : selectIndexRepresentatives) {
//					assert equalityInformation.isRepresentative(selectIndexRepresentative) : "no representative: " + selectIndexRepresentative;
//					final Term replacementStoreIndex = rawIndex2replacedIndex.get(store2NewArray.getKey().getIndex());
//					assert !occursIn(eliminatee, replacementStoreIndex) : "var is still there";
//					final Term replacementSelectIndex = rawIndex2replacedIndex.get(selectIndexRepresentative);
//					assert !occursIn(eliminatee, replacementSelectIndex) : "var is still there";
//					final Term indexEquality = QuantifierUtils.applyDerOperator(mgdScript.getScript(),
//							quantifier, replacementStoreIndex, replacementSelectIndex);
//					final Term newSelect = mgdScript.getScript().term("select", store2NewArray.getValue(), replacementSelectIndex);
//					final Term storeValueReplacement = new SubstitutionWithLocalSimplification(mgdScript, substitutionMapping).transform(store2NewArray.getKey().getValue());
//					final Term newValueInCell = QuantifierUtils.applyDerOperator(mgdScript.getScript(),
//							quantifier, newSelect, storeValueReplacement);
//					final EqualityStatus indexEqStatus = equalityInformation.getEqualityStatus(store2NewArray.getKey().getIndex(), selectIndexRepresentative);
//					switch (indexEqStatus) {
//					case EQUAL:
//						// this means not equal for univeral quantification
//						resultConjuncts1case.add(newValueInCell);
//						continue;
//					case NOT_EQUAL:
//						// case handled via substitution
//						continue;
//					case UNKNOWN: {
//						final Term oldSelect = constructOldSelectTerm(mgdScript, eliminatee, selectIndexRepresentative);
//						if (equalityInformation.getEqualityStatus(oldSelect, store2NewArray.getKey().getValue()) == EqualityStatus.EQUAL) {
//							resultConjuncts1case.add(newValueInCell);
//							continue;
//						}
//
//						final Term succedent = newValueInCell;
//						final Term negatedAntecedent = SmtUtils.not(mgdScript.getScript(), indexEquality);
//						final Term positiveCase = QuantifierUtils.applyCorrespondingFiniteConnective(mgdScript.getScript(),
//								quantifier, negatedAntecedent, succedent);
//						resultConjuncts2cases.add(positiveCase);
//					}
//					{
//						final Term oldCellValue = oldCellMapping.get(selectIndexRepresentative).getFirst();
//						final Term oldValueInCell = QuantifierUtils.applyDerOperator(mgdScript.getScript(),
//								quantifier, newSelect, oldCellValue);
//						final Term negatedAntecedent = indexEquality;
//						final Term negativeCase = QuantifierUtils.applyCorrespondingFiniteConnective(mgdScript.getScript(),
//								quantifier, negatedAntecedent, oldValueInCell);
//						resultConjuncts2cases.add(negativeCase);
//						break;
//					}
//					default:
//						throw new AssertionError();
//					}
//
//				}
//			}
//			return new Pair<List<Term>, List<Term>>(resultConjuncts1case, resultConjuncts2cases);
//		}

		private static Term findNiceReplacementForRepresentative(final Term rep,
				final TermVariable eliminatee, final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
			assert equalityInformation.isRepresentative(rep) : "Not representative " + rep;
			final Set<Term> eq = equalityInformation.getEquivalenceClass(rep);
			final List<Term> list = eq.stream().filter(x -> !occursIn(eliminatee, x)).collect(Collectors.toList());
			if (list.isEmpty()) {
				return null;
			} else {
				
			}
			Collections.sort(list, FEWER_VARIABLE_FIRST);
			return list.get(0);
		}

		private static Term constructOldSelectTerm(final ManagedScript mgdScript, final TermVariable eliminatee, final Term index) {
			return mgdScript.getScript().term("select", eliminatee, index);
		}


		private class AuxVarConstructor {
			private final Set<TermVariable> mConstructedAuxVars = new HashSet<>();

			public TermVariable constructAuxVar(final String purpose, final Sort sort) {
				final TermVariable auxVar = mMgdScript.constructFreshTermVariable(purpose, sort);
				mConstructedAuxVars.add(auxVar);
				return auxVar;
			}

			public Set<TermVariable> getConstructedAuxVars() {
				return mConstructedAuxVars;
			}

		}

		/**
		 * Let eliminatee be the array that is eliminated and (select eliminatee idx
		 * v) a select term. If idx contains eliminatee, we have to replace idx by
		 * an auxiliary variable. As an optimization, we only construct one
		 * auxiliary variable for each equivalence class of indices.
		 */
		private class IndexMappingProvider {

			private final Map<Term, Term> mIndexReplacementMapping = new HashMap<>();
			private final List<Term> mIndexMappingDefinitions = new ArrayList<>();

			public IndexMappingProvider(final List<Term> indexRepresentatives, final TermVariable eliminatee,
					final ThreeValuedEquivalenceRelation<Term> equalityInformation,
					final AuxVarConstructor auxVarConstructor, final int quantifier) {

				final IValueConstruction<Term, TermVariable> valueConstruction = new IValueConstruction<Term, TermVariable>() {

					@Override
					public TermVariable constructValue(final Term index) {
						final TermVariable indexReplacement = auxVarConstructor.constructAuxVar(AUX_VAR_INDEX,
								index.getSort());
						return indexReplacement;
					}

				};
				final ConstructionCache<Term, TermVariable> cc = new ConstructionCache<>(valueConstruction);
				for (final Term index : indexRepresentatives) {
					final Term eqTerm = findNiceReplacementForRepresentative(index, eliminatee, equalityInformation);
					if (eqTerm != null) {
						mIndexReplacementMapping.put(index, eqTerm);
					} else {
						// need to introduce auxiliary variable
						final Term indexRepresentative = equalityInformation.getRepresentative(index);
						final TermVariable indexReplacement = cc.getOrConstruct(indexRepresentative);
						mIndexReplacementMapping.put(index, indexReplacement);
						mIndexMappingDefinitions.add(QuantifierUtils.applyDerOperator(mScript, quantifier,
								indexReplacement, index));
					}
				}
			}



			public Map<Term, Term> getIndexReplacementMapping() {
				return mIndexReplacementMapping;
			}

			public List<Term> getIndexMappingDefinitions() {
				return mIndexMappingDefinitions;
			}

		}


		public class ValueEqualityChecker {
			final TermVariable mEliminatee;
			final Term mStoreIndex;
			final Term mStoreValue;
			final ThreeValuedEquivalenceRelation<Term> mIndices;
			final ManagedScript mMgdScript;
			final IncrementalPlicationChecker mIncrementalPlicationChecker;
			final Map<Term, Term> mOldCellMapping;
			final List<Term> mValueEqualities = new ArrayList<>();

			public ValueEqualityChecker(final TermVariable eliminatee, final Term storeIndex, final Term storeValue,
					final ThreeValuedEquivalenceRelation<Term> indices, final ManagedScript mgdScript,
					final IncrementalPlicationChecker incrementalPlicationChecker, final Map<Term, Term> oldCellMapping) {
				super();
				mEliminatee = eliminatee;
				mStoreIndex = storeIndex;
				mStoreValue = storeValue;
				mIndices = indices;
				mMgdScript = mgdScript;
				mIncrementalPlicationChecker = incrementalPlicationChecker;
				mOldCellMapping = oldCellMapping;
			}

			public boolean isDistinguishworthyIndexPair(final Term index1, final Term index2) {
				final Term select1 = mMgdScript.getScript().term("select", mEliminatee, index1);
				final Term select2 = mMgdScript.getScript().term("select", mEliminatee, index2);
				final Term eq = SmtUtils.binaryEquality(mMgdScript.getScript(), select1, select2);
				final Validity cellEqVal = mIncrementalPlicationChecker.checkPlication(eq);
				if (cellEqVal == Validity.VALID) {
					final boolean distinguishworthy1 = processStoreIndex(index1, index2, select2);
					final boolean distinguishworthy2 = processStoreIndex(index2, index1, select1);
					if (distinguishworthy1 && distinguishworthy2) {
						return true;
					} else {
						final Term cellEq = SmtUtils.binaryEquality(mMgdScript.getScript(), mOldCellMapping.get(index1),
								mOldCellMapping.get(index2));
						mValueEqualities.add(cellEq);
						return false;
					}
				} else {
					return true;
				}
			}

			private boolean processStoreIndex(final Term storeIndexCandidate, final Term otherIndex,
					final Term otherSelect) {
				if (isStoreIndex(storeIndexCandidate)) {
					final Term storeEq = SmtUtils.binaryEquality(mMgdScript.getScript(), mStoreValue, otherSelect);
					final Validity storeEqVal = mIncrementalPlicationChecker.checkPlication(storeEq);
					if (storeEqVal == Validity.VALID) {
						final Term storeCellEq = SmtUtils.binaryEquality(mMgdScript.getScript(), mStoreValue,
								mOldCellMapping.get(otherIndex));
						mValueEqualities.add(storeCellEq);
						return false;
					} else {
						return true;
					}
				} else {
					return false;
				}
			}

			boolean isStoreIndex(final Term index1) {
				if (mStoreIndex == null) {
					return false;
				} else {
					return mIndices.getRepresentative(index1).equals(mIndices.getRepresentative(mStoreIndex));
				}
			}

			public List<Term> getValueEqualities() {
				return mValueEqualities;
			}
			



}

		private class EqProvider {
			private final Term[] mContext;
			private final TermVariable mEliminatee;
			private final int mQuantifier;

			public EqProvider(final Term inputTerm, final TermVariable eliminatee, final int quantifier) {
				mContext = QuantifierUtils.getXjunctsInner(quantifier, inputTerm);
				mEliminatee = eliminatee;
				mQuantifier = quantifier;
			}

			public Term getEqTerm(final Term term) {
				final EqualityInformation eqInfo = EqualityInformation.getEqinfo(mScript, term, mContext, mEliminatee,
						mQuantifier);
				if (eqInfo == null) {
					return null;
				} else {
					return eqInfo.getTerm();
				}
			}
		}

		
		private interface IEqualityChecker {
			public EqualityStatus checkEquality(Term term1, Term term2);
		}
		
		private class LocalSimplificationsEqualityChecker implements IEqualityChecker {

			@Override
			public EqualityStatus checkEquality(final Term term1, final Term term2) {
				final Term eq = SmtUtils.binaryEquality(mScript, term1, term2);
				if (SmtUtils.isTrue(eq)) {
					return EqualityStatus.EQUAL;
				} else if (SmtUtils.isFalse(eq)) {
					return EqualityStatus.NOT_EQUAL;
				} else {
					return EqualityStatus.UNKNOWN;
				}
			}
			
		}
		
		
		private class CheapIncompleteIndexValueAnalyzer {
			
		}


}