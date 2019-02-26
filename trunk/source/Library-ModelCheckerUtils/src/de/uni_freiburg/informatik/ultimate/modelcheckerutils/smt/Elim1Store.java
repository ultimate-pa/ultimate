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
import java.util.TreeSet;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayOccurrenceAnalysis;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArraySelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelectOverStoreEliminationUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.pqe.EqualityInformation;
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

	private static final Comparator<ArrayIndex> INDEX_WITH_FEWER_VARIABLE_FIRST = new Comparator<ArrayIndex>() {

		@Override
		public int compare(final ArrayIndex o1, final ArrayIndex o2) {
			return o2.getFreeVars().size() - o1.getFreeVars().size();
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

	private static final boolean SELECT_OVER_STORE_PREPROCESSING = true;


	public Elim1Store(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final int quantifier) {
		super();
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
	}

	public EliminationTask elim1(final int quantifier, final TermVariable eliminatee, final Term inputTerm,
			final Term context) {
		assert UltimateNormalFormUtils.respectsUltimateNormalForm(inputTerm) : "invalid input";
		assert (!Arrays.asList(context.getFreeVars()).contains(eliminatee)) : "eliminatee must not occur in context";
		final Term[] xjunctsOuter = QuantifierUtils.getXjunctsOuter(quantifier, inputTerm);
		if (xjunctsOuter.length > 1) {
			throw new AssertionError("several disjuncts! " + inputTerm);
		}

		ArrayOccurrenceAnalysis aoa = new ArrayOccurrenceAnalysis(inputTerm, eliminatee);
//		if (!aoa.getArrayDisequalities().isEmpty()) {
//			throw new AssertionError("disequality");
//		}
//		if (!aoa.getArrayEqualities().isEmpty()) {
//			throw new AssertionError("equality");
//		}
		final TreeSet<Integer> dims = aoa.computeSelectAndStoreDimensions();
		if (dims.size() > 1) {
			throw new AssertionError("Dims before preprocessing " + dims);
		}


		if (SELECT_OVER_STORE_PREPROCESSING) {
			final List<MultiDimensionalSelectOverNestedStore> mdsoss = MultiDimensionalSelectOverNestedStore
					.extractMultiDimensionalSelectOverStores(inputTerm, eliminatee);
			if (!mdsoss.isEmpty()) {
				final Term polarizedContext;
				if (quantifier == QuantifiedFormula.EXISTS) {
					polarizedContext = context;
				} else if (quantifier == QuantifiedFormula.FORALL) {
					polarizedContext = SmtUtils.not(mScript, context);
				} else {
					throw new AssertionError("unknown quantifier");
				}
				final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<>();
				final ArrayIndexEqualityManager aiem = new ArrayIndexEqualityManager(tver, polarizedContext, quantifier,
						mLogger, mMgdScript);
				final MultiDimensionalSelectOverNestedStore mdsos = mdsoss.get(0);
				final Term replaced = MultiDimensionalSelectOverStoreEliminationUtils.replace(mMgdScript, aiem,
						inputTerm, mdsos);
				aiem.unlockSolver();
				return new EliminationTask(quantifier, Collections.singleton(eliminatee), replaced);
			}
		}


		final Set<TermVariable> newAuxVars = new LinkedHashSet<>();
		Term preprocessedInput;

		{
			// anti-DER preprocessing

			final ArrayEqualityExplicator aadk = new ArrayEqualityExplicator(mMgdScript, quantifier, eliminatee,
					inputTerm, aoa.getAntiDerRelations(quantifier));
			final Term antiDerPreprocessed = aadk.getResultTerm();
			newAuxVars.addAll(aadk.getNewAuxVars());

			aoa = new ArrayOccurrenceAnalysis(antiDerPreprocessed, eliminatee);

			final TreeSet<Integer> dims2 = aoa.computeSelectAndStoreDimensions();
			if (dims.size() > 1) {
				throw new AssertionError("Dims after anti-DER " + dims2);
			}

			final DerPreprocessor dp = new DerPreprocessor(mServices, mMgdScript, quantifier, eliminatee,
					antiDerPreprocessed, aoa.getDerRelations(quantifier));
			newAuxVars.addAll(dp.getNewAuxVars());
			preprocessedInput = dp.getResult();
			if (dp.introducedDerPossibility()) {
				// do DER
				final EliminationTask afterDer = ElimStorePlain.applyNonSddEliminations(mServices, mMgdScript,
						new EliminationTask(quantifier, Collections.singleton(eliminatee), preprocessedInput),
						PqeTechniques.ONLY_DER);
				newAuxVars.addAll(afterDer.getEliminatees());
				return new EliminationTask(quantifier, newAuxVars, afterDer.getTerm());
			}

		}
		aoa = new ArrayOccurrenceAnalysis(preprocessedInput, eliminatee);

		final List<MultiDimensionalSelect> selectTerms = aoa.getArraySelects();

		final List<MultiDimensionalStore> stores = aoa.getNestedArrayStores();


		final Term polarizedContext;
		if (quantifier == QuantifiedFormula.EXISTS) {
			polarizedContext = context;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			polarizedContext = SmtUtils.not(mScript, context);
		} else {
			throw new AssertionError("unknown quantifier");
		}
		final Term preprocessedInputWithContext = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
				preprocessedInput, polarizedContext);

		final ThreeValuedEquivalenceRelation<Term> equalityInformation = ArrayIndexEqualityUtils
				.collectComplimentaryEqualityInformation(mMgdScript.getScript(), quantifier,
						preprocessedInputWithContext, selectTerms, stores);
		if (equalityInformation == null) {
			final Term absobingElement = QuantifierUtils.getNeutralElement(mScript, quantifier);
			mLogger.warn("Array PQE input equivalent to " + absobingElement);
			return new EliminationTask(quantifier, Collections.emptySet(), absobingElement);
		}

		final Set<ArrayIndex> selectIndices = new HashSet<>();
		for (final MultiDimensionalSelect selectTerm : selectTerms) {
			selectIndices.add(selectTerm.getIndex());
		}

		final ArrayIndexEqualityManager aiem = new ArrayIndexEqualityManager(equalityInformation, preprocessedInput,
				quantifier, mLogger, mMgdScript);

		final long startTime = System.nanoTime();
		final ThreeValuedEquivalenceRelation<ArrayIndex> analysisResult = analyzeIndexEqualities(quantifier,
				selectIndices, stores, preprocessedInputWithContext, equalityInformation, eliminatee, mMgdScript, aiem);
		final long durationMs = (System.nanoTime() - startTime) / 1_000_000;
		if (durationMs > 100) {
			mLogger.info("Index analysis took " + durationMs + " ms");
		}
		if (aiem.contextIsAbsorbingElement()) {
			final Term absobingElement = QuantifierUtils.getNeutralElement(mScript, quantifier);
			mLogger.warn("Array PQE input equivalent to " + absobingElement);
			return new EliminationTask(quantifier, Collections.emptySet(), absobingElement);
		}
		assert analysisResult != null;

		final List<ArrayIndex> selectIndexRepresentatives = new ArrayList<>();
		final List<ArrayIndex> allIndexRepresentatives = new ArrayList<>();
		for (final ArrayIndex selectIndex : selectIndices) {
			final ArrayIndex selectIndexRepresentative = analysisResult.getRepresentative(selectIndex);
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
		final List<ArrayIndex> storeIndexRepresentatives = new ArrayList<>();
		for (final MultiDimensionalStore store : stores) {
			final ArrayIndex storeIndexRepresentative = analysisResult.getRepresentative(store.getIndex());
			storeIndexRepresentatives.add(storeIndexRepresentative);
			allIndexRepresentatives.add(storeIndexRepresentative);
		}


		final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation = analysisResult;
		final Term indexEqualityInformationTerm = indexEquivalencesToTerm(mScript, indexEqualityInformation,
				quantifier);

		final AuxVarConstructor auxVarConstructor = new AuxVarConstructor();
		final IndexMappingProvider imp = new IndexMappingProvider(allIndexRepresentatives, eliminatee,
				indexEqualityInformation, auxVarConstructor, quantifier);

		final Map<ArrayIndex, ArrayIndex> indexMapping = imp.getIndexReplacementMapping();
		final List<Term> indexMappingDefinitions = imp.getIndexMappingDefinitions();

		final Term indexDefinitionsTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
				indexMappingDefinitions);
		final Term intermediateTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
				indexDefinitionsTerm, preprocessedInput, indexEqualityInformationTerm);

		final Map<MultiDimensionalStore, Term> newArrayMapping = new HashMap<>();
		for (final MultiDimensionalStore store : stores) {
			final Term newArray;
			final EqProvider eqProvider = new EqProvider(preprocessedInputWithContext, eliminatee, quantifier);
			final Term eqArray = eqProvider.getEqTerm(store.toTerm(mScript));
			if (eqArray != null) {
				newArray = eqArray;
			} else {
				newArray = auxVarConstructor.constructAuxVar(AUX_VAR_NEW_ARRAY, eliminatee.getSort());
			}
			newArrayMapping.put(store, newArray);
		}

		final Map<ArrayIndex, Term> oldCellMapping = constructOldCellValueMapping(selectIndexRepresentatives,
				newArrayMapping, equalityInformation, indexMapping, auxVarConstructor, eliminatee, quantifier,
				indexEqualityInformation, mScript);
		newAuxVars.addAll(auxVarConstructor.getConstructedAuxVars());

		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final Entry<MultiDimensionalStore, Term> entry : newArrayMapping.entrySet()) {
			assert entry.getKey().toTerm(mScript).getSort() == entry.getValue().getSort() : "incompatible sorts";
			substitutionMapping.put(entry.getKey().toTerm(mScript), entry.getValue());
		}
		for (final ArrayIndex selectIndex : selectIndices) {
			final Term oldSelect = constructOldSelectTerm(mMgdScript, eliminatee, selectIndex);
			final ArrayIndex indexRepresentative = indexEqualityInformation.getRepresentative(selectIndex);
			if (oldCellMapping.containsKey(indexRepresentative)) {
				assert oldSelect.getSort() == oldCellMapping.get(indexRepresentative).getSort() : "incompatible sorts";
				substitutionMapping.put(oldSelect, oldCellMapping.get(indexRepresentative));
			} else {
				throw new AssertionError("should be dead code by now");
				// final Term newSelect = mMgdScript.getScript().term("select", newArray,
				// indexRepresentative);
				// substitutionMapping.put(oldSelect, newSelect);
			}
		}

		final List<Term> singleCaseJuncts = new ArrayList<>();
		final List<Term> doubleCaseJuncts = new ArrayList<>();

		final Pair<List<Term>, List<Term>> wc = constructWriteConstraints(selectIndexRepresentatives,
				indexEqualityInformation, mMgdScript, indexMapping, oldCellMapping, eliminatee, quantifier,
				newArrayMapping, substitutionMapping, equalityInformation);
		singleCaseJuncts.addAll(wc.getFirst());
		doubleCaseJuncts.addAll(wc.getSecond());

		final Pair<List<Term>, List<Term>> cc = constructIndexValueConnection(selectIndexRepresentatives,
				indexEqualityInformation, mMgdScript, indexMapping, oldCellMapping, eliminatee, quantifier,
				equalityInformation);
		singleCaseJuncts.addAll(cc.getFirst());
		doubleCaseJuncts.addAll(cc.getSecond());

		final Term singleCaseTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, singleCaseJuncts);

		final Term transformedTerm = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping)
				.transform(intermediateTerm);
		final Term storedValueInformation = constructStoredValueInformation(quantifier, eliminatee, newArrayMapping,
				indexMapping, substitutionMapping, indexEqualityInformation);
		Term result = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, transformedTerm,
				storedValueInformation, singleCaseTerm);
		if (!doubleCaseJuncts.isEmpty()) {
			final Term doubleCaseTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
					doubleCaseJuncts);
			final Term doubleCaseTermMod;
			if (APPLY_DOUBLE_CASE_SIMPLIFICATION) {
				final boolean contextIsDisjunctive = (quantifier == QuantifiedFormula.FORALL);
				final Term resultWithContext = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, result,
						context);
				doubleCaseTermMod = new SimplifyDDAWithTimeout(mScript, false, mServices, result, contextIsDisjunctive)
						.getSimplifiedTerm(doubleCaseTerm);
			} else {
				doubleCaseTermMod = doubleCaseTerm;
			}
			result = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, result, doubleCaseTermMod);
		}
		if (Arrays.asList(result.getFreeVars()).contains(eliminatee)) {
			throw new AssertionError("var is still there: " + eliminatee + " input size " + new DagSizePrinter(result)
					+ " context size " + new DagSizePrinter(result) + " output size " + new DagSizePrinter(result));
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
			sb.append(String.format(", treesize of input %d treesize of output %d", new DAGSize().treesize(inputTerm),
					new DAGSize().treesize(result)));
			mLogger.info(sb.toString());
		}
		final EliminationTask resultEt;
		if (APPLY_RESULT_SIMPLIFICATION) {
			if (DEBUG_CRASH_ON_LARGE_SIMPLIFICATION_POTENTIAL) {
				final ExtendedSimplificationResult esrQuick = SmtUtils.simplifyWithStatistics(mMgdScript, result,
						mServices, SimplificationTechnique.SIMPLIFY_QUICK);
				mLogger.info(String.format("quick treesize reduction %d that is %2.1f percent of original size",
						esrQuick.getReductionOfTreeSize(), esrQuick.getReductionRatioInPercent()));
				if (esrQuick.getReductionRatioInPercent() < 70) {
					throw new AssertionError(
							"Reduction: " + esrQuick.getReductionRatioInPercent() + " Input: " + preprocessedInput);
				}
			}
			final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mMgdScript, result, mServices,
					SimplificationTechnique.SIMPLIFY_DDA);
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
		assert !DEBUG_EXTENDED_RESULT_CHECK
				|| EliminationTask
						.areDistinct(mMgdScript.getScript(), resultEt,
								new EliminationTask(quantifier, Collections.singleton(eliminatee),
										inputTerm)) != LBool.SAT : "Bug array QE Input: " + inputTerm + " Result:"
												+ resultEt;
		return resultEt;

	}



	private static Term indexEquivalencesToTerm(final Script script,
			final ThreeValuedEquivalenceRelation<ArrayIndex> tver, final int quantifier) {
		final List<Term> elementEqualities = tver.getSupportingEqualities().entrySet().stream()
				.map(en -> ArrayIndex.constructDerRelation(script, quantifier, en.getKey(), en.getValue()))
				.collect(Collectors.toList());
		final List<Term> elementDisequalities = tver.getDisequalities().entrySet().stream()
				.map(pair -> ArrayIndex.constructAntiDerRelation(script, quantifier, pair.getKey(), pair.getValue()))
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
	 * @param script
	 */
	private static Map<ArrayIndex, Term> constructOldCellValueMapping(final List<ArrayIndex> selectIndexRepresentatives,
			final Map<MultiDimensionalStore, Term> newArrayMapping,
			final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final Map<ArrayIndex, ArrayIndex> indexMapping, final AuxVarConstructor auxVarConstructor,
			final TermVariable eliminatee, final int quantifier,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation, final Script script) {
		final IValueConstruction<MultiDimensionalSelect, TermVariable> valueConstruction = new IValueConstruction<MultiDimensionalSelect, TermVariable>() {

			@Override
			public TermVariable constructValue(final MultiDimensionalSelect mds) {
				final TermVariable oldCell = auxVarConstructor.constructAuxVar(AUX_VAR_ARRAYCELL,
						mds.toTerm(script).getSort());
				return oldCell;
			}

		};
		final ConstructionCache<MultiDimensionalSelect, TermVariable> cc = new ConstructionCache<>(valueConstruction);
		final Map<ArrayIndex, Term> oldCellMapping = new HashMap<>();
		for (final ArrayIndex selectIndexRepresentative : selectIndexRepresentatives) {
			Term oldCellValue;
			final Term oldValueInNewArray = getOldValueInNewArray(newArrayMapping, indexEqualityInformation,
					indexMapping, selectIndexRepresentative, script);
			if (oldValueInNewArray != null) {
				oldCellValue = oldValueInNewArray;
			} else {
				oldCellValue = constructOldCellValue(equalityInformation, eliminatee, cc, selectIndexRepresentative, script);
			}
			oldCellMapping.put(selectIndexRepresentative, oldCellValue);
		}
		return oldCellMapping;
	}

	private static Term getOldValueInNewArray(final Map<MultiDimensionalStore, Term> newArrayMapping,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation,
			final Map<ArrayIndex, ArrayIndex> indexMapping, final ArrayIndex selectIndexRepresentative,
			final Script script) {
		for (final Entry<MultiDimensionalStore, Term> entry : newArrayMapping.entrySet()) {
			final ArrayIndex storeIndex = entry.getKey().getIndex();
			if (indexEqualityInformation.getEqualityStatus(selectIndexRepresentative,
					storeIndex) == EqualityStatus.NOT_EQUAL) {
				final ArrayIndex replacementSelectIndex = indexMapping.get(selectIndexRepresentative);
				final Term newAuxArray = entry.getValue();
				final Term newSelect = new MultiDimensionalSelect(newAuxArray, replacementSelectIndex, script)
						.toTerm(script);
				return newSelect;
			}
		}
		return null;
	}

	private static Term constructOldCellValue(final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final TermVariable eliminatee, final ConstructionCache<MultiDimensionalSelect, TermVariable> cc,
			final ArrayIndex selectIndexRepresentative, final Script script) {
		Term oldCellValue;
		{
			final MultiDimensionalSelect oldSelect = new MultiDimensionalSelect(eliminatee, selectIndexRepresentative,
					script);
			final Term oldSelectRepresentative = equalityInformation.getRepresentative(oldSelect.toTerm(script));
			final Term eqTerm = findNiceReplacementForRepresentative(oldSelectRepresentative, eliminatee,
					equalityInformation);
			if (eqTerm != null) {
				oldCellValue = eqTerm;
			} else {
				final TermVariable oldCellVariable = cc.getOrConstruct(oldSelect);
				oldCellValue = oldCellVariable;
			}
		}
		return oldCellValue;
	}


	private static ThreeValuedEquivalenceRelation<ArrayIndex> analyzeIndexEqualities(final int mQuantifier,
			final Set<ArrayIndex> selectIndices, final List<MultiDimensionalStore> stores, final Term preprocessedInput,
			final ThreeValuedEquivalenceRelation<Term> tver, final TermVariable eliminatee,
			final ManagedScript mgdScript, final ArrayIndexEqualityManager aiem) {

		mgdScript.getScript().echo(new QuotedObject("starting to analyze index equalities"));

		if (aiem.contextIsAbsorbingElement()) {
			aiem.unlockSolver();
			return null;
		}

		final ArrayList<ArrayIndex> allIndicesList = new ArrayList<>(selectIndices);
		for (final MultiDimensionalStore store : stores) {
			allIndicesList.add(store.getIndex());
		}

		final List<Term> allValues = new ArrayList<>();
		final Map<Term, ArrayIndex> value2selectIndex = new HashMap<>();
		final Map<ArrayIndex, Term> selectIndex2value = new HashMap<>();
		for (final ArrayIndex selectIndex : selectIndices) {
			final Term oldSelect = constructOldSelectTerm(mgdScript, eliminatee, selectIndex);
			allValues.add(oldSelect);
			value2selectIndex.put(oldSelect, selectIndex);
			selectIndex2value.put(selectIndex, oldSelect);
		}
		for (final MultiDimensionalStore arrayStore : stores) {
			allValues.add(arrayStore.getValue());
		}

		final ThreeValuedEquivalenceRelation<ArrayIndex> result = new ThreeValuedEquivalenceRelation<>();
		for (int i = 0; i < allIndicesList.size(); i++) {
			result.addElement(allIndicesList.get(i));
		}
		for (int i = 0; i < allIndicesList.size(); i++) {
			for (int j = i + 1; j < allIndicesList.size(); j++) {
				// TODO: try to obtain equal term with few variables
				final ArrayIndex index1 = allIndicesList.get(i);
				final ArrayIndex index2 = allIndicesList.get(j);
				final EqualityStatus eq = aiem.checkIndexEquality(index1, index2);
				switch (eq) {
				case EQUAL:
					result.reportEquality(index1, index2);
					break;
				case NOT_EQUAL:
					result.reportDisequality(index1, index2);
					break;
				case UNKNOWN:
					// report nothing
					break;
				default:
					throw new AssertionError("illegal EqualityStatus " + eq);
				}
			}
		}
		// unclear if these additional checks are useful

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
				aiem.checkEqualityStatus(value1, value2);
			}
		}

		aiem.unlockSolver();
		// mMgdScript.requestLockRelease();
		mgdScript.getScript().echo(new QuotedObject("finished analysis of index equalities"));
		return result;
	}






	private Term constructStoredValueInformation(final int quantifier, final TermVariable eliminatee,
			final Map<MultiDimensionalStore, Term> newArrayMapping, final Map<ArrayIndex, ArrayIndex> indexMapping,
			final Map<Term, Term> substitutionMapping,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation) {
		final List<Term> storedValueInformation = new ArrayList<>();
		for (final Entry<MultiDimensionalStore, Term> entry : newArrayMapping.entrySet()) {
			final ArrayIndex indexRepresentative = indexEqualityInformation
					.getRepresentative(entry.getKey().getIndex());
			final ArrayIndex replacementIndex = indexMapping.get(indexRepresentative);
			storedValueInformation.add(QuantifierUtils.applyDerOperator(mMgdScript.getScript(), quantifier,
					new MultiDimensionalSelect(entry.getValue(), replacementIndex, mScript).toTerm(mScript),
					new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping)
							.transform(entry.getKey().getValue())));
		}
		return QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, storedValueInformation);
	}

	private static boolean occursIn(final TermVariable tv, final ArrayIndex index) {
		return index.stream().anyMatch(x -> occursIn(tv, x));
	}

	private static boolean occursIn(final TermVariable tv, final Term term) {
		return Arrays.asList(term.getFreeVars()).contains(tv);
	}

	/**
	 * <ul>
	 * <li>∀k∈Idx. i == k ==> oldCell_i == oldCell_k)
	 * <li>(i != storeIndex) ==> (aNew[i] == oldCell_i)
	 * </ul>
	 *
	 * @param equalityInformation
	 */
	private static Pair<List<Term>, List<Term>> constructIndexValueConnection(
			final List<ArrayIndex> selectIndexRepresentatives,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation, final ManagedScript mgdScript,
			final Map<ArrayIndex, ArrayIndex> indexMapping, final Map<ArrayIndex, Term> oldCellMapping,
			final TermVariable eliminatee, final int quantifier,
			final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
		final List<Term> resultConjuncts1case = new ArrayList<Term>();
		final List<Term> resultConjuncts2cases = new ArrayList<Term>();
		for (int i = 0; i < selectIndexRepresentatives.size(); i++) {
			for (int j = i + 1; j < selectIndexRepresentatives.size(); j++) {
				if (!indexEqualityInformation.isRepresentative(selectIndexRepresentatives.get(j))) {
					throw new AssertionError("representatives only");
				}
				final ArrayIndex index1 = selectIndexRepresentatives.get(i);
				final ArrayIndex index2 = selectIndexRepresentatives.get(j);
				if (false && selectTermsWithsimilarArray(oldCellMapping.get(index1), oldCellMapping.get(index2))) {
					// 2017-11-22 Matthias: Bug report from Marius shows that
					// this is unsound. Maybe we can introduce it again later
					// but we need the indices on the other array are equivalent
					// to the indices on this array.

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
					final ArrayIndex replacementIndex1 = indexMapping.get(index1);
					assert !occursIn(eliminatee, replacementIndex1) : "var is still there";
					final ArrayIndex replacementIndex2 = indexMapping.get(index2);
					assert !occursIn(eliminatee, replacementIndex2) : "var is still there";
					indexEqualityTerm = ArrayIndex.constructDerRelation(mgdScript.getScript(), quantifier,
							replacementIndex1, replacementIndex2);
					break;
				default:
					throw new AssertionError();
				}

				final Term valueEqualityTerm;
				final Term oldSelect1 = constructOldSelectTerm(mgdScript, eliminatee, index1);
				final Term oldSelect2 = constructOldSelectTerm(mgdScript, eliminatee, index2);
				final EqualityStatus valueEqualityStatus = equalityInformation.getEqualityStatus(oldSelect1,
						oldSelect2);
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
				case UNKNOWN: {
					final Term value1 = oldCellMapping.get(index1);
					assert !occursIn(eliminatee, value1) : "var is still there";
					final Term value2 = oldCellMapping.get(index2);
					assert !occursIn(eliminatee, value2) : "var is still there";
					valueEqualityTerm = QuantifierUtils.applyDerOperator(mgdScript.getScript(), quantifier, value1,
							value2);
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
		 * @param equalityInformation
		 */
	private static Pair<List<Term>, List<Term>> constructWriteConstraints(
			final List<ArrayIndex> selectIndexRepresentatives,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation, final ManagedScript mgdScript,
			final Map<ArrayIndex, ArrayIndex> indexMapping, final Map<ArrayIndex, Term> oldCellMapping,
			final TermVariable eliminatee, final int quantifier, final Map<MultiDimensionalStore, Term> newArrayMapping,
			final Map<Term, Term> substitutionMapping, final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
		final List<Term> resultConjuncts1case = new ArrayList<Term>();
		final List<Term> resultConjuncts2cases = new ArrayList<Term>();
		for (final Entry<MultiDimensionalStore, Term> entry : newArrayMapping.entrySet()) {
			ArrayIndex storeIndexRepresentative;
			{
				final ArrayIndex storeIndex = entry.getKey().getIndex();
				storeIndexRepresentative = indexEqualityInformation.getRepresentative(storeIndex);
			}
			final Term storeValue = entry.getKey().getValue();
			final Term newAuxArray = entry.getValue();
			for (final ArrayIndex selectIndexRepresentative : selectIndexRepresentatives) {
				assert indexEqualityInformation.isRepresentative(selectIndexRepresentative) : "no representative: "
						+ selectIndexRepresentative;
				final ArrayIndex replacementStoreIndex = indexMapping.get(storeIndexRepresentative);
				assert !occursIn(eliminatee, replacementStoreIndex) : "var is still there";
				final ArrayIndex replacementSelectIndex = indexMapping.get(selectIndexRepresentative);
				assert !occursIn(eliminatee, replacementSelectIndex) : "var is still there";
				final Term indexEquality = ArrayIndex.constructDerRelation(mgdScript.getScript(), quantifier,
						replacementStoreIndex, replacementSelectIndex);

				final MultiDimensionalSelect newSelect = new MultiDimensionalSelect(newAuxArray, replacementSelectIndex,
						mgdScript.getScript());
				final Term storeValueReplacement = new SubstitutionWithLocalSimplification(mgdScript,
						substitutionMapping).transform(storeValue);
				final Term newValueInCell = QuantifierUtils.applyDerOperator(mgdScript.getScript(), quantifier,
						newSelect.toTerm(mgdScript.getScript()), storeValueReplacement);
				final EqualityStatus indexEqStatus = indexEqualityInformation
						.getEqualityStatus(storeIndexRepresentative, selectIndexRepresentative);
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
				} {
					final Term oldCellValue = oldCellMapping.get(selectIndexRepresentative);
					final Term oldValueInCell = QuantifierUtils.applyDerOperator(mgdScript.getScript(), quantifier,
							newSelect.toTerm(mgdScript.getScript()), oldCellValue);
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


	private static Term findNiceReplacementForRepresentative(final Term term, final TermVariable eliminatee,
			final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
		assert equalityInformation.isRepresentative(term) : "Not representative " + term;
		final Set<Term> eq = equalityInformation.getEquivalenceClass(term);
		final List<Term> list = eq.stream().filter(x -> !occursIn(eliminatee, x)).collect(Collectors.toList());
		if (list.isEmpty()) {
			return null;
		} else {

		}
		Collections.sort(list, FEWER_VARIABLE_FIRST);
		return list.get(0);
	}

	private static ArrayIndex findNiceReplacementForRepresentative(final ArrayIndex index,
			final TermVariable eliminatee, final ThreeValuedEquivalenceRelation<ArrayIndex> equalityInformation) {
		assert equalityInformation.isRepresentative(index) : "Not representative " + index;
		final Set<ArrayIndex> eq = equalityInformation.getEquivalenceClass(index);
		final List<ArrayIndex> list = eq.stream().filter(x -> !occursIn(eliminatee, x)).collect(Collectors.toList());
		if (list.isEmpty()) {
			return null;
		} else {

		}
		Collections.sort(list, INDEX_WITH_FEWER_VARIABLE_FIRST);
		return list.get(0);
	}

	private static Term constructOldSelectTerm(final ManagedScript mgdScript, final TermVariable eliminatee,
			final ArrayIndex selectIndex) {
		return new MultiDimensionalSelect(eliminatee, selectIndex, mgdScript.getScript()).toTerm(mgdScript.getScript());
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
	 * Let eliminatee be the array that is eliminated and (select eliminatee idx v)
	 * a select term. If idx contains eliminatee, we have to replace idx by an
	 * auxiliary variable. As an optimization, we only construct one auxiliary
	 * variable for each equivalence class of indices.
	 */
	private class IndexMappingProvider {

		private final Map<ArrayIndex, ArrayIndex> mIndexReplacementMapping = new HashMap<>();
		private final List<Term> mIndexMappingDefinitions = new ArrayList<>();

		public IndexMappingProvider(final List<ArrayIndex> allIndexRepresentatives, final TermVariable eliminatee,
				final ThreeValuedEquivalenceRelation<ArrayIndex> equalityInformation,
				final AuxVarConstructor auxVarConstructor, final int quantifier) {

			final IValueConstruction<ArrayIndex, ArrayIndex> valueConstruction = new IValueConstruction<ArrayIndex, ArrayIndex>() {

				@Override
				public ArrayIndex constructValue(final ArrayIndex index) {
					final List<Term> indexEntries = new ArrayList<>();
					for (int i = 0; i < index.size(); i++) {
						final TermVariable entryReplacement = auxVarConstructor
								.constructAuxVar("dim" + i + AUX_VAR_INDEX, index.get(i).getSort());
						indexEntries.add(entryReplacement);
					}
					return new ArrayIndex(indexEntries);
				}

			};
			final ConstructionCache<ArrayIndex, ArrayIndex> cc = new ConstructionCache<>(valueConstruction);
			for (final ArrayIndex index : allIndexRepresentatives) {
				final ArrayIndex eqTerm = findNiceReplacementForRepresentative(index, eliminatee, equalityInformation);
				if (eqTerm != null) {
					mIndexReplacementMapping.put(index, eqTerm);
				} else {
					// need to introduce auxiliary variable
					final ArrayIndex indexRepresentative = equalityInformation.getRepresentative(index);
					final ArrayIndex indexReplacement = cc.getOrConstruct(indexRepresentative);
					mIndexReplacementMapping.put(index, indexReplacement);
					mIndexMappingDefinitions
							.add(ArrayIndex.constructDerRelation(mScript, quantifier, indexReplacement, index));
				}
			}
		}

		public Map<ArrayIndex, ArrayIndex> getIndexReplacementMapping() {
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
			final Term select1 = SmtUtils.select(mMgdScript.getScript(), mEliminatee, index1);
			final Term select2 = SmtUtils.select(mMgdScript.getScript(), mEliminatee, index2);
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
				return eqInfo.getRelatedTerm();
			}
		}
	}




}