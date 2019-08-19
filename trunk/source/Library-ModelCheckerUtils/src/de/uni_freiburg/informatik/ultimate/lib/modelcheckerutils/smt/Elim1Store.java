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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt;

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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayOccurrenceAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArraySelect;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.EqualityInformation;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
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

	public EliminationTaskWithContext elim1(final EliminationTaskWithContext input) {
		final Term inputTerm = input.getTerm();
		if (!QuantifierUtils.isQuantifierFree(inputTerm)) {
			throw new AssertionError("Alternating quantifiers not yet supported");
		}
		if (input.getEliminatees().size() != 1) {
			throw new IllegalArgumentException("Can only eliminate one variable");
		}
		final int quantifier = input.getQuantifier();
		final TermVariable eliminatee = input.getEliminatees().iterator().next();
		final Term context = input.getContext();

		assert UltimateNormalFormUtils.respectsUltimateNormalForm(inputTerm) : "invalid input";
//		assert (!Arrays.asList(context.getFreeVars()).contains(eliminatee)) : "eliminatee must not occur in context";
		final Term[] xjunctsOuter = QuantifierUtils.getXjunctsOuter(quantifier, inputTerm);
//		if (xjunctsOuter.length > 1) {
//			throw new AssertionError("several disjuncts! " + inputTerm);
//		}

		ArrayOccurrenceAnalysis aoa = new ArrayOccurrenceAnalysis(mMgdScript.getScript(), inputTerm, eliminatee);
//		if (!aoa.getArrayDisequalities().isEmpty()) {
//			throw new AssertionError("disequality");
//		}
//		if (!aoa.getArrayEqualities().isEmpty()) {
//			throw new AssertionError("equality");
//		}
		final TreeSet<Integer> dims = aoa.computeSelectAndStoreDimensions();
//		if (dims.size() > 1) {
//			throw new AssertionError("Dims before preprocessing " + dims);
//		}


		final Term polarizedContext = QuantifierUtils.negateIfUniversal(mServices, mMgdScript, quantifier, context);


		final Set<TermVariable> newAuxVars = new LinkedHashSet<>();
		final Term preprocessedInput = input.getTerm();

		aoa = new ArrayOccurrenceAnalysis(mMgdScript.getScript(), preprocessedInput, eliminatee)
				.downgradeDimensionsIfNecessary(mMgdScript.getScript());
		assert aoa.computeSelectAndStoreDimensions().size() <= 1 : "incompatible";

		final List<MultiDimensionalSelect> selectTerms = aoa.getArraySelects();
		final List<MultiDimensionalNestedStore> stores = aoa.getNestedArrayStores();

		final ThreeValuedEquivalenceRelation<Term> equalityInformation = ArrayIndexEqualityUtils
				.collectComplimentaryEqualityInformation(mMgdScript.getScript(), quantifier,
						polarizedContext, selectTerms, stores);
		if (equalityInformation == null) {
			final Term absobingElement = QuantifierUtils.getNeutralElement(mScript, quantifier);
			mLogger.warn("Array PQE input equivalent to " + absobingElement);
			return new EliminationTaskWithContext(quantifier, Collections.emptySet(), absobingElement, input.getContext());
		}

		final Set<ArrayIndex> selectIndices = new HashSet<>();
		for (final MultiDimensionalSelect selectTerm : selectTerms) {
			selectIndices.add(selectTerm.getIndex());
		}

		final ArrayIndexEqualityManager aiem = new ArrayIndexEqualityManager(equalityInformation, polarizedContext,
				quantifier, mLogger, mMgdScript);
		if (aiem.contextIsAbsorbingElement()) {
			aiem.unlockSolver();
			final Term absobingElement = QuantifierUtils.getNeutralElement(mScript, quantifier);
			mLogger.warn("Array PQE input equivalent to " + absobingElement);
			return new EliminationTaskWithContext(quantifier, Collections.emptySet(), absobingElement,
					input.getContext());
		}

		final long startTime = System.nanoTime();
		final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation = analyzeIndexEqualities(quantifier,
				selectIndices, stores, polarizedContext, equalityInformation, eliminatee, mMgdScript, aiem);
		final long durationMs = (System.nanoTime() - startTime) / 1_000_000;
		if (durationMs > 100) {
			mLogger.info("Index analysis took " + durationMs + " ms");
		}
		assert indexEqualityInformation != null;

		// inferences of select term equalities might lead
		// to better index replacements because a select term
		// might be part of an index
		inferCellEqualitiesViaCongruence(mMgdScript, eliminatee, indexEqualityInformation, equalityInformation);

		final List<ArrayIndex> selectIndexRepresentatives = new ArrayList<>();
		for (final ArrayIndex selectIndex : selectIndices) {
			final ArrayIndex selectIndexRepresentative = indexEqualityInformation.getRepresentative(selectIndex);
			selectIndexRepresentatives.add(selectIndexRepresentative);
		}


		final AuxVarConstructor auxVarConstructor = new AuxVarConstructor();
		final IndexMappingProvider imp = new IndexMappingProvider(mMgdScript, eliminatee,
				indexEqualityInformation);

		final Map<ArrayIndex, ArrayIndex> indexMapping = imp.getIndexReplacementMapping();

		newAuxVars.addAll(imp.getConstructedAuxVars());
		final Term indexAuxVarDefinitionsTerm = imp.constructAuxVarDefinitions(mScript, quantifier);

		final Map<MultiDimensionalNestedStore, Term> newArrayMapping = new HashMap<>();
		final Term preprocessedInputWithContext = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
				preprocessedInput, polarizedContext);
		for (final MultiDimensionalNestedStore store : stores) {
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
		for (final Entry<MultiDimensionalNestedStore, Term> entry : newArrayMapping.entrySet()) {
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

		final Pair<List<Term>, List<Term>> wc = constructWriteConstraints2(selectIndexRepresentatives,
				indexEqualityInformation, mMgdScript, indexMapping, oldCellMapping, eliminatee, quantifier,
				newArrayMapping, substitutionMapping, equalityInformation, aiem);
		singleCaseJuncts.addAll(wc.getFirst());
		doubleCaseJuncts.addAll(wc.getSecond());

		final Pair<List<Term>, List<Term>> cc = constructIndexValueConnection(selectIndexRepresentatives,
				indexEqualityInformation, mMgdScript, indexMapping, oldCellMapping, eliminatee, quantifier,
				equalityInformation, aiem);
		singleCaseJuncts.addAll(cc.getFirst());
		doubleCaseJuncts.addAll(cc.getSecond());

		aiem.unlockSolver();
		final Term indexEqualityInformationTerm = indexEquivalencesToTerm(mScript, indexEqualityInformation,
				quantifier, aiem);
		assert indexEqualityInformationTerm == QuantifierUtils.getAbsorbingElement(mScript, quantifier) : "strange equivalences";
		final Term intermediateTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
				indexAuxVarDefinitionsTerm, preprocessedInput);

		final Term singleCaseTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, singleCaseJuncts);

		final Term transformedTerm = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping)
				.transform(intermediateTerm);
//		final Term storedValueInformation = constructStoredValueInformation(quantifier, eliminatee, newArrayMapping,
//				indexMapping, substitutionMapping, indexEqualityInformation);
		Term result = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, transformedTerm,
				singleCaseTerm);
		if (!doubleCaseJuncts.isEmpty()) {
			final Term doubleCaseTerm = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
					doubleCaseJuncts);
			final Term doubleCaseTermMod;
			if (APPLY_DOUBLE_CASE_SIMPLIFICATION) {
				final Term resultWithContext = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, result,
						context);
				final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mMgdScript, doubleCaseTerm,
						QuantifierUtils.negateIfUniversal(mServices, mMgdScript, quantifier, resultWithContext), mServices,
						SimplificationTechnique.SIMPLIFY_DDA);
				final String sizeMessage = String.format("treesize reduction %d, result has %2.1f percent of original size",
						esr.getReductionOfTreeSize(), esr.getReductionRatioInPercent());
				mLogger.info(sizeMessage);
				doubleCaseTermMod = esr.getSimplifiedTerm();
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
		final EliminationTaskWithContext resultEt;
		if (APPLY_RESULT_SIMPLIFICATION) {
			if (DEBUG_CRASH_ON_LARGE_SIMPLIFICATION_POTENTIAL) {
				final ExtendedSimplificationResult esrQuick = SmtUtils.simplifyWithStatistics(mMgdScript, result,
						null, mServices, SimplificationTechnique.SIMPLIFY_QUICK);
				mLogger.info(String.format("quick treesize reduction %d that is %2.1f percent of original size",
						esrQuick.getReductionOfTreeSize(), esrQuick.getReductionRatioInPercent()));
				if (esrQuick.getReductionRatioInPercent() < 70) {
					throw new AssertionError(
							"Reduction: " + esrQuick.getReductionRatioInPercent() + " Input: " + preprocessedInput);
				}
			}
			final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mMgdScript, result, null,
					mServices, SimplificationTechnique.SIMPLIFY_DDA);
			final Term simplified = esr.getSimplifiedTerm();
			final String sizeMessage = String.format("treesize reduction %d that is %2.1f percent of original size",
					esr.getReductionOfTreeSize(), esr.getReductionRatioInPercent());
			if (esr.getReductionRatioInPercent() <= 70) {
				mLogger.info(sizeMessage);
			} else {
				mLogger.info(sizeMessage);
			}
			mLogger.info("treesize after simplification " + new DAGSize().treesize(simplified));
			resultEt = new EliminationTaskWithContext(quantifier, newAuxVars, simplified, input.getContext());
		} else {
			resultEt = new EliminationTaskWithContext(quantifier, newAuxVars, result, input.getContext());
		}
		assert !DEBUG_EXTENDED_RESULT_CHECK
				|| EliminationTask
						.areDistinct(mMgdScript.getScript(), resultEt,
								new EliminationTask(quantifier, Collections.singleton(eliminatee),
										inputTerm)) != LBool.SAT : "Bug array QE Input: " + inputTerm + " Result:"
												+ resultEt;
		return resultEt;

	}


	/**
	 * Add for each pair of equivalent indices i1, i2, the equality
	 * select(i1)==select(i2). Even if the equalityInformation
	 * {@link ThreeValuedEquivalenceRelation} was obtained by
	 * a congruence aware reasoning, this information might be new
	 * because the select terms might have not been in the
	 * {@link ThreeValuedEquivalenceRelation} before.
	 */
	private static void inferCellEqualitiesViaCongruence(final ManagedScript mgdScript, final TermVariable eliminatee,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation,
			final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
		for (final Entry<ArrayIndex, ArrayIndex> supp : indexEqualityInformation.getSupportingEqualities().entrySet()) {
			final ArrayIndex lhsIndex = supp.getKey();
			final ArrayIndex rhsIndex = supp.getValue();
			final Term lhsSelect = constructOldSelectTerm(mgdScript, eliminatee, lhsIndex);
			final Term rhsSelect = constructOldSelectTerm(mgdScript, eliminatee, rhsIndex);
			equalityInformation.addElement(lhsSelect);
			equalityInformation.addElement(rhsSelect);
			equalityInformation.reportEquality(lhsSelect, rhsSelect);
		}
	}



	private static Term indexEquivalencesToTerm(final Script script,
			final ThreeValuedEquivalenceRelation<ArrayIndex> tver, final int quantifier, final ArrayIndexEqualityManager aiem) {
		final List<Term> elementEqualities = tver.getSupportingEqualities().entrySet().stream()
				.map(en -> aiem.constructDerRelation(script, quantifier, en.getKey(), en.getValue()))
				.collect(Collectors.toList());
		final List<Term> elementDisequalities = tver.getDisequalities().entrySet().stream()
				.map(pair -> aiem.constructAntiDerRelation(script, quantifier, pair.getKey(), pair.getValue()))
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
			final Map<MultiDimensionalNestedStore, Term> newArrayMapping,
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

	private static Term getOldValueInNewArray(final Map<MultiDimensionalNestedStore, Term> newArrayMapping,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation,
			final Map<ArrayIndex, ArrayIndex> indexMapping, final ArrayIndex selectIndexRepresentative,
			final Script script) {
		return null;
//		for (final Entry<MultiDimensionalNestedStore, Term> entry : newArrayMapping.entrySet()) {
//			final ArrayIndex storeIndex = entry.getKey().getIndex();
//			if (indexEqualityInformation.getEqualityStatus(selectIndexRepresentative,
//					storeIndex) == EqualityStatus.NOT_EQUAL) {
//				final ArrayIndex replacementSelectIndex = indexMapping.get(selectIndexRepresentative);
//				final Term newAuxArray = entry.getValue();
//				final Term newSelect = new MultiDimensionalSelect(newAuxArray, replacementSelectIndex, script)
//						.toTerm(script);
//				return newSelect;
//			}
//		}
//		return null;
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
			final Set<ArrayIndex> selectIndices, final List<MultiDimensionalNestedStore> stores, final Term preprocessedInput,
			final ThreeValuedEquivalenceRelation<Term> tver, final TermVariable eliminatee,
			final ManagedScript mgdScript, final ArrayIndexEqualityManager aiem) {

		mgdScript.getScript().echo(new QuotedObject("starting to analyze index equalities"));

		if (aiem.contextIsAbsorbingElement()) {
			aiem.unlockSolver();
			return null;
		}

		final ArrayList<ArrayIndex> allIndicesList = new ArrayList<>(selectIndices);
		for (final MultiDimensionalNestedStore store : stores) {
			allIndicesList.addAll(store.getIndices());
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
		for (final MultiDimensionalNestedStore arrayStore : stores) {
			allValues.addAll(arrayStore.getValues());
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
	 * @param aiem
	 */
	private static Pair<List<Term>, List<Term>> constructIndexValueConnection(
			final List<ArrayIndex> selectIndexRepresentatives,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation, final ManagedScript mgdScript,
			final Map<ArrayIndex, ArrayIndex> indexMapping, final Map<ArrayIndex, Term> oldCellMapping,
			final TermVariable eliminatee, final int quantifier,
			final ThreeValuedEquivalenceRelation<Term> equalityInformation, final ArrayIndexEqualityManager aiem) {
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
					indexEqualityTerm = aiem.constructDerRelation(mgdScript.getScript(), quantifier,
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
		 * @param aiem
		 */
	private static Pair<List<Term>, List<Term>> constructWriteConstraints(
			final List<ArrayIndex> selectIndexRepresentatives,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation, final ManagedScript mgdScript,
			final Map<ArrayIndex, ArrayIndex> indexMapping, final Map<ArrayIndex, Term> oldCellMapping,
			final TermVariable eliminatee, final int quantifier, final Map<MultiDimensionalStore, Term> newArrayMapping,
			final Map<Term, Term> substitutionMapping, final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final ArrayIndexEqualityManager aiem) {
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
				final Term indexEquality = aiem.constructDerRelation(mgdScript.getScript(), quantifier,
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


	/**
	 * <ul>
	 * <li> (i == storeIndex)==> (aNew[i] == newValue)
	 * <li> (i != storeIndex) ==> (aNew[i] == oldCell_i)
	 * </ul>
	 * @param equalityInformation
	 * @param aiem
	 */
	private static Pair<List<Term>, List<Term>> constructWriteConstraints2(
			final List<ArrayIndex> selectIndexRepresentatives,
			final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation, final ManagedScript mgdScript,
			final Map<ArrayIndex, ArrayIndex> indexMapping, final Map<ArrayIndex, Term> oldCellMapping,
			final TermVariable eliminatee, final int quantifier, final Map<MultiDimensionalNestedStore, Term> newArrayMapping,
			final Map<Term, Term> substitutionMapping, final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final ArrayIndexEqualityManager aiem) {
		final List<Term> resultConjuncts1case = new ArrayList<Term>();
		final List<Term> resultConjuncts2cases = new ArrayList<Term>();
		for (final Entry<MultiDimensionalNestedStore, Term> entry : newArrayMapping.entrySet()) {
			final List<ArrayIndex> storeIndexReplacements = new ArrayList<>();
			final List<Term> storeValueReplacements = new ArrayList<>();
			final Term resArray = entry.getValue();
			for (int i=0; i<entry.getKey().getIndices().size(); i++) {
				ArrayIndex storeIndexRepresentative;
				{
					final ArrayIndex storeIndex = entry.getKey().getIndices().get(i);
					storeIndexRepresentative = indexEqualityInformation.getRepresentative(storeIndex);
				}
				final ArrayIndex replacementStoreIndex = indexMapping.get(storeIndexRepresentative);
				assert !occursIn(eliminatee, replacementStoreIndex) : "var is still there";

				final Term storeValue = entry.getKey().getValues().get(i);
				final Term storeValueReplacement = new SubstitutionWithLocalSimplification(mgdScript,
						substitutionMapping).transform(storeValue);
				storeIndexReplacements.add(replacementStoreIndex);
				storeValueReplacements.add(storeValueReplacement);
			}
			for (final ArrayIndex selectIndexRepresentative : selectIndexRepresentatives) {
				assert indexEqualityInformation.isRepresentative(selectIndexRepresentative) : "no representative: "
						+ selectIndexRepresentative;
				final ArrayIndex selectIndexReplacement = indexMapping.get(selectIndexRepresentative);
				assert !occursIn(eliminatee, selectIndexReplacement) : "var is still there";

				final Term inputArrayValue = oldCellMapping.get(selectIndexRepresentative);
				final Term constraintForSelectIndex = aiem.constructNestedStoreUpdateConstraint(mgdScript.getScript(),
						quantifier, resArray, selectIndexReplacement, storeIndexReplacements, storeValueReplacements,
						inputArrayValue);
				if (SmtUtils.isAtomicFormula(constraintForSelectIndex)) {
					resultConjuncts1case.add(constraintForSelectIndex);
				} else {
					resultConjuncts2cases.add(constraintForSelectIndex);
				}
			}
			final Set<ArrayIndex> storeIndexRepresentatives = new HashSet<>();
			for (final ArrayIndex storeIndex : entry.getKey().getIndices()) {
				storeIndexRepresentatives.add(indexEqualityInformation.getRepresentative(storeIndex));
			}
			for (final ArrayIndex storeIndexRepresentative : storeIndexRepresentatives) {
				assert indexEqualityInformation.isRepresentative(storeIndexRepresentative) : "no representative: "
						+ storeIndexRepresentative;
				final ArrayIndex storeIndexReplacement = indexMapping.get(storeIndexRepresentative);
				assert !occursIn(eliminatee, storeIndexReplacement) : "var is still there";

				final Term defaultValue = null;
				final Term constraintForStoreIndex = aiem.constructNestedStoreUpdateConstraint(mgdScript.getScript(),
						quantifier, resArray, storeIndexReplacement, storeIndexReplacements, storeValueReplacements,
						defaultValue);
				if (SmtUtils.isAtomicFormula(constraintForStoreIndex)) {
					resultConjuncts1case.add(constraintForStoreIndex);
				} else {
					resultConjuncts2cases.add(constraintForStoreIndex);
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
	private static class IndexMappingProvider {

		private final ArrayIndexReplacementConstructor mReplacementConstructor;
		private final Map<ArrayIndex, ArrayIndex> mIndexReplacementMapping = new HashMap<>();

		public IndexMappingProvider(final ManagedScript mgdScript,
				final TermVariable eliminatee, final ThreeValuedEquivalenceRelation<ArrayIndex> indexEqualityInformation) {

			mReplacementConstructor = new ArrayIndexReplacementConstructor(mgdScript, AUX_VAR_INDEX, eliminatee);

			for (final ArrayIndex index : indexEqualityInformation.getAllRepresentatives()) {
				final ArrayIndex eqTerm = findNiceReplacementForRepresentative(index, eliminatee, indexEqualityInformation);
				if (eqTerm != null) {
					mIndexReplacementMapping.put(index, eqTerm);
				} else {
					// need to introduce auxiliary variables
					final ArrayIndex indexRepresentative = indexEqualityInformation.getRepresentative(index);
					final ArrayIndex indexReplacement = mReplacementConstructor
							.constructIndexReplacementIfNeeded(indexRepresentative);
					mIndexReplacementMapping.put(index, indexReplacement);
				}
			}
		}

		public Map<ArrayIndex, ArrayIndex> getIndexReplacementMapping() {
			return mIndexReplacementMapping;
		}

		public Term constructAuxVarDefinitions(final Script script, final int quantifier) {
			return mReplacementConstructor.constructDefinitions(script, quantifier);
		}

		public Set<TermVariable> getConstructedAuxVars() {
			return mReplacementConstructor.getConstructedAuxVars();
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