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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays;

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
import java.util.Stack;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtLibUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayEqualityExplicator;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndexBasedCostEstimation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndexEqualityManager;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayOccurrenceAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelectOverStoreEliminationUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.EliminationTaskPlain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.EliminationTaskSimple;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeHashRelation;

/**
 * TODO 2017-10-17 Matthias: The following documentation is outdated.
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
public class ElimStorePlain {

	private static final boolean RETURN_AFTER_SOS = false;
	private static final boolean TRANSFORM_TO_XNF_ON_SPLIT = false;
	private static final boolean THROW_ELIMINATION_EXCEPTIONS = false;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private int mRecursiveCallCounter = -1;

	public ElimStorePlain(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		super();
		mMgdScript = mgdScript;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(SmtLibUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
	}

	/**
	 * Old, iterative elimination. Is sound but if we cannot eliminate all
	 * quantifiers it sometimes produces a large number of similar
	 * disjuncts/conjuncts that is too large for simplification.
	 * @throws ElimStorePlainException
	 *
	 */
	public EliminationTaskSimple elimAll(final EliminationTaskSimple eTask) {
		try {

			final Stack<EliminationTaskSimple> taskStack = new Stack<>();
			final ArrayList<Term> resultDisjuncts = new ArrayList<>();
			final Set<TermVariable> resultEliminatees = new LinkedHashSet<>();
			{
				final EliminationTaskSimple eliminationTask = new EliminationTaskSimple(eTask.getQuantifier(),
						eTask.getEliminatees(), eTask.getTerm());
				pushTaskOnStack(eliminationTask, taskStack);
			}
			int numberOfRounds = 0;
			while (!taskStack.isEmpty()) {
				final EliminationTaskSimple currentETask = taskStack.pop();
				final TreeHashRelation<Integer, TermVariable> tr = classifyEliminatees(currentETask.getEliminatees());

				final LinkedHashSet<TermVariable> arrayEliminatees = getArrayTvSmallDimensionsFirst(tr);

				if (arrayEliminatees.isEmpty()) {
					// no array eliminatees left
					resultDisjuncts.add(currentETask.getTerm());
					resultEliminatees.addAll(currentETask.getEliminatees());
				} else {
					TermVariable thisIterationEliminatee;
					{
						final Iterator<TermVariable> it = arrayEliminatees.iterator();
						thisIterationEliminatee = it.next();
						it.remove();
					}
					final EliminationTaskPlain etwc = new EliminationTaskPlain(currentETask.getQuantifier(),
							Collections.singleton(thisIterationEliminatee), currentETask.getTerm(), null);
					final EliminationTaskSimple ssdElimRes = new Elim1Store(mMgdScript, mServices, eTask.getQuantifier())
							.elim1(etwc);
					arrayEliminatees.addAll(ssdElimRes.getEliminatees());
					// also add non-array eliminatees
					arrayEliminatees.addAll(tr.getImage(0));
					final EliminationTaskPlain eliminationTask1 = new EliminationTaskPlain(
							ssdElimRes.getQuantifier(), arrayEliminatees, ssdElimRes.getTerm(), null);
					final EliminationTaskPlain eliminationTask2 = applyNonSddEliminations(mServices, mMgdScript,
							eliminationTask1, PqeTechniques.ALL_LOCAL);
					if (mLogger.isInfoEnabled()) {
						mLogger.info("Start of round: " + printVarInfo(tr) + " End of round: "
								+ printVarInfo(classifyEliminatees(eliminationTask2.getEliminatees())) + " and "
								+ QuantifierUtils.getCorrespondingFiniteJuncts(eTask.getQuantifier(), eliminationTask2.getTerm()).length
								+ " xjuncts.");
					}
					// assert (!maxSizeIncrease(tr,
					// classifyEliminatees(eliminationTask2.getEliminatees()))) : "number of max-dim
					// elements increased!";

					pushTaskOnStack(eliminationTask2, taskStack);
				}
				numberOfRounds++;
			}
			mLogger.info("Needed " + numberOfRounds + " rounds to eliminate " + eTask.getEliminatees().size()
					+ " variables, produced " + resultDisjuncts.size() + " xjuncts");
			// return term and variables that we could not eliminate
			return new EliminationTaskSimple(eTask.getQuantifier(), resultEliminatees,
					QuantifierUtils.applyCorrespondingFiniteConnective(mMgdScript.getScript(), eTask.getQuantifier(),
							resultDisjuncts));
		} catch (final ElimStorePlainException e) {
			if (THROW_ELIMINATION_EXCEPTIONS) {
				throw new UnsupportedOperationException(e);
			} else {
				return new EliminationTaskSimple(eTask.getQuantifier(), new HashSet<>(eTask.getEliminatees()),
						eTask.getTerm());
			}
		}
	}

	/**
	 * New recursive elimination. Public method for starting the algorithm, not
	 * suitable for recursive calls.
	 * @throws ElimStorePlainException
	 */
	public EliminationTaskSimple startRecursiveElimination(final EliminationTaskSimple eTask) {
		final TreeHashRelation<Integer, TermVariable> tr = classifyEliminatees(eTask.getEliminatees());
		if (tr.isEmpty() || (tr.getDomain().size() == 1 && tr.getDomain().contains(0))) {
			// return immediately if we do not have quantified arrays.
			return eTask;
		}
		mRecursiveCallCounter = 0;
		final long inputSize = new DAGSize().treesize(eTask.getTerm());
		// Initially, the context is "true" (context is independent quantifier)
		final Term initialContext = mMgdScript.getScript().term("true");
		EliminationTaskSimple result;
		try {
			result = doElimAllRec(new EliminationTaskPlain(eTask.getQuantifier(),
					eTask.getEliminatees(), eTask.getTerm(), initialContext));
			final long outputSize = new DAGSize().treesize(result.getTerm());
			// TODO 2019-02-20 Matthias: If implementation is more matured then show this
			// output only if there was a big increase in the size of the formula.
			mLogger.info(String.format(
					"Needed %s recursive calls to eliminate %s variables, input treesize:%s, output treesize:%s",
					mRecursiveCallCounter, eTask.getEliminatees().size(), inputSize, outputSize));
			return result;
		} catch (final ElimStorePlainException e) {
			if (THROW_ELIMINATION_EXCEPTIONS) {
				throw new UnsupportedOperationException(e);
			} else {
				assert !mMgdScript.isLocked() : "Solver still locked";
				return new EliminationTaskSimple(eTask.getQuantifier(), new HashSet<>(eTask.getEliminatees()), eTask.getTerm());
			}
		}
	}


	private EliminationTaskPlain doElimOneRec(final EliminationTaskPlain eTask) throws ElimStorePlainException {
		if (QuantifierUtils.getCorrespondingFiniteJuncts(eTask.getQuantifier(), eTask.getTerm()).length != 1) {
			throw new AssertionError("Input not split");
		}
		// input one ?
		// split in disjunction
		// elim1store, output many
		// apply non-sdd on new only
		// classify, recurse, result array free, put results together
		// classify, recurse, result array free, put results together
		// ...
		assert eTask.getEliminatees().size() == 1;
		final TermVariable eliminatee = eTask.getEliminatees().iterator().next();
		assert SmtSortUtils.isArraySort(eliminatee.getSort());

//		final ArrayOccurrenceAnalysis aoa = new ArrayOccurrenceAnalysis(eTask.getTerm(), eliminatee);

		final Pair<Term[], Term> split = split(eTask.getQuantifier(), eliminatee, eTask.getTerm());
		final Term additionalContext = QuantifierUtils.negateIfUniversal(mServices, mMgdScript, eTask.getQuantifier(),
				split.getSecond());
		final Term totalContext = SmtUtils.and(mMgdScript.getScript(), eTask.getContext(), additionalContext);
		final EliminationTaskPlain resultOfRecursiveCall;
		if (split.getFirst().length != 1) {
//			throw new AssertionError("new split possibility");
			resultOfRecursiveCall = eliminateOne(new EliminationTaskPlain(eTask.getQuantifier(),
					eTask.getEliminatees(), QuantifierUtils.applyCorrespondingFiniteConnective(mMgdScript.getScript(),
							eTask.getQuantifier(), split.getFirst()),
					totalContext));
		} else {
			assert split.getFirst().length == 1;
			final EliminationTaskPlain revisedInput = new EliminationTaskPlain(eTask.getQuantifier(),
					eTask.getEliminatees(), split.getFirst()[0], totalContext);
			// final EliminationTaskWithContext revisedInput = new
			// EliminationTaskWithContext(eTask.getQuantifier(),
			// eTask.getEliminatees(), eTask.getTerm(), totalContext);

			final EliminationTaskPlain ssdElimRes = applyComplexEliminationRules(mServices, mLogger, mMgdScript, revisedInput);
			final EliminationTaskPlain eliminationTask2 = applyNonSddEliminations(mServices, mMgdScript,
					ssdElimRes, PqeTechniques.ALL_LOCAL);
			resultOfRecursiveCall = doElimAllRec(eliminationTask2);
		}
		final Term resultTerm = QuantifierUtils.applyDualFiniteConnective(mMgdScript.getScript(),
				eTask.getQuantifier(), resultOfRecursiveCall.getTerm(), split.getSecond());
		return new EliminationTaskPlain(resultOfRecursiveCall.getQuantifier(),
				resultOfRecursiveCall.getEliminatees(), resultTerm, eTask.getContext());
	}

	public static EliminationTaskPlain applyComplexEliminationRules(final IUltimateServiceProvider services,
			final ILogger logger, final ManagedScript mgdScript, final EliminationTaskPlain eTask)
			throws ElimStorePlainException {
		if (!QuantifierUtils.isQuantifierFree(eTask.getTerm())) {
			throw new AssertionError("Alternating quantifiers not yet supported");
		}
		final TermVariable eliminatee;
		if (eTask.getEliminatees().size() != 1) {
			throw new AssertionError("need exactly one eliminatee");
		} else {
			eliminatee = eTask.getEliminatees().iterator().next();
		}
		final Term polarizedContext = QuantifierUtils.negateIfUniversal(services, mgdScript,
				eTask.getQuantifier(), eTask.getContext());
		final ArrayOccurrenceAnalysis aoa = new ArrayOccurrenceAnalysis(mgdScript.getScript(), eTask.getTerm(), eliminatee);
		if (!aoa.getValueOfStore().isEmpty() || !aoa.getOtherFunctionApplications().isEmpty()) {
			// cannot eliminated this array
			return null;
		}
		final Term[] dualJuncts = QuantifierUtils.getDualFiniteJuncts(eTask.getQuantifier(), eTask.getTerm());
		final Map<Boolean, List<Term>> part = Arrays.stream(dualJuncts).collect(Collectors
				.partitioningBy(x -> QuantifierUtils.isCorrespondingFiniteJunction(eTask.getQuantifier(), x)));
		final Term distributers = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), eTask.getQuantifier(), part.get(true));
		final ArrayOccurrenceAnalysis resetAoa = new ArrayOccurrenceAnalysis(mgdScript.getScript(), distributers, eliminatee);
		if (!resetAoa.getDerRelations(eTask.getQuantifier()).isEmpty() || !resetAoa.getAntiDerRelations(eTask.getQuantifier()).isEmpty()) {
			return null;
		}

		final Set<TermVariable> newAuxVars = new LinkedHashSet<>();

		// Step 1: DER preprocessing
		final Term termAfterDerPreprocessing;
		final ArrayOccurrenceAnalysis aoaAfterDerPreprocessing;
		if (aoa.getDerRelations(eTask.getQuantifier()).isEmpty()) {
			termAfterDerPreprocessing = eTask.getTerm();
			aoaAfterDerPreprocessing = aoa;
		} else {
			final DerPreprocessor de;
			{
				final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<>();
				final ArrayIndexEqualityManager aiem = new ArrayIndexEqualityManager(tver, polarizedContext,
						eTask.getQuantifier(), logger, mgdScript);
				try {
					de = new DerPreprocessor(services, mgdScript, eTask.getQuantifier(), eliminatee, eTask.getTerm(),
							aoa.getDerRelations(eTask.getQuantifier()), aiem);
				} catch (final ElimStorePlainException espe) {
					aiem.unlockSolver();
					throw espe;
				}
				aiem.unlockSolver();
			}
			newAuxVars.addAll(de.getNewAuxVars());
			termAfterDerPreprocessing = de.getResult();
			if (de.introducedDerPossibility()) {
				// do DER
				final EliminationTaskPlain afterDer = ElimStorePlain.applyNonSddEliminations(services,
						mgdScript, new EliminationTaskPlain(eTask.getQuantifier(),
								Collections.singleton(eliminatee), termAfterDerPreprocessing, eTask.getContext()),
						PqeTechniques.ONLY_DER);
				if (!afterDer.getEliminatees().isEmpty()) {
					throw new AssertionError(" unsuccessful DER");
				}
				newAuxVars.addAll(afterDer.getEliminatees());
				return new EliminationTaskPlain(eTask.getQuantifier(), newAuxVars, afterDer.getTerm(),
						eTask.getContext());
			} else {
				aoaAfterDerPreprocessing = new ArrayOccurrenceAnalysis(mgdScript.getScript(), termAfterDerPreprocessing, eliminatee);
				newAuxVars.add(eliminatee);
			}
		}

		// Step 2: anti-DER preprocessing
		final Term termAfterAntiDerPreprocessing;
		final ArrayOccurrenceAnalysis aoaAfterAntiDerPreprocessing;
		if (aoa.getAntiDerRelations(eTask.getQuantifier()).isEmpty()) {
			termAfterAntiDerPreprocessing = termAfterDerPreprocessing;
			aoaAfterAntiDerPreprocessing = aoaAfterDerPreprocessing;
		} else {
			final ArrayEqualityExplicator aadk = new ArrayEqualityExplicator(mgdScript, eTask.getQuantifier(), eliminatee,
					termAfterDerPreprocessing, aoa.getAntiDerRelations(eTask.getQuantifier()));
			termAfterAntiDerPreprocessing = aadk.getResultTerm();
			newAuxVars.addAll(aadk.getNewAuxVars());
			aoaAfterAntiDerPreprocessing = new ArrayOccurrenceAnalysis(mgdScript.getScript(), termAfterAntiDerPreprocessing, eliminatee);
			if (!varOccurs(eliminatee, termAfterAntiDerPreprocessing)) {
				return new EliminationTaskPlain(eTask.getQuantifier(), newAuxVars, termAfterAntiDerPreprocessing,
						eTask.getContext());
			}
		}

		// Step 3: select-over-store preprocessing
		final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<>();
		final ArrayIndexEqualityManager aiem = new ArrayIndexEqualityManager(tver, polarizedContext, eTask.getQuantifier(),
				logger, mgdScript);
		ArrayOccurrenceAnalysis sosAoa = aoaAfterAntiDerPreprocessing;
		Term sosTerm = termAfterAntiDerPreprocessing;
		while (!sosAoa.getArraySelectOverStores().isEmpty()) {
			final MultiDimensionalSelectOverNestedStore mdsos = sosAoa.getArraySelectOverStores().get(0);
			final Term replaced = MultiDimensionalSelectOverStoreEliminationUtils.replace(mgdScript, aiem,
					sosTerm, mdsos);
			final Term replacedInNnf = new NnfTransformer(mgdScript, services, QuantifierHandling.KEEP).transform(replaced);
			sosTerm = replacedInNnf;
			sosAoa = new ArrayOccurrenceAnalysis(mgdScript.getScript(), sosTerm, eliminatee);
			if(!varOccurs(eliminatee, replacedInNnf) || RETURN_AFTER_SOS) {
				aiem.unlockSolver();
				return new EliminationTaskPlain(eTask.getQuantifier(), newAuxVars,
						replacedInNnf, eTask.getContext());
			}
		}
		aiem.unlockSolver();
		final Term termAfterSos = sosTerm;
		final ArrayOccurrenceAnalysis aoaAfterSos = sosAoa;


		final EliminationTaskPlain eTaskForStoreElimination = new EliminationTaskPlain(
				eTask.getQuantifier(), Collections.singleton(eliminatee), termAfterSos,
				eTask.getContext());
		final EliminationTaskPlain resOfStoreElimination = new Elim1Store(mgdScript, services,
				eTask.getQuantifier()).elim1(eTaskForStoreElimination);
		// if (res.getEliminatees().contains(eliminatee)) {
		// throw new AssertionError("elimination failed");
		// }
		newAuxVars.addAll(resOfStoreElimination.getEliminatees());
		final EliminationTaskPlain eliminationResult = new EliminationTaskPlain(eTask.getQuantifier(),
				newAuxVars, resOfStoreElimination.getTerm(), eTask.getContext());
		return eliminationResult;
	}

	private static boolean varOccurs(final TermVariable var, final Term term) {
		return Arrays.stream(term.getFreeVars()).anyMatch(x -> (x == var));
	}

	private EliminationTaskPlain doElimAllRec(final EliminationTaskPlain eTask)
			throws ElimStorePlainException {
		mRecursiveCallCounter++;
		final int thisRecursiveCallNumber = mRecursiveCallCounter;

		final TreeHashRelation<Integer, TermVariable> tr = classifyEliminatees(eTask.getEliminatees());
		Term currentTerm = eTask.getTerm();


		// Set of newly introduced quantified variables
		final Set<TermVariable> newElimnatees = new LinkedHashSet<>();
		for (final int dim : tr.getDomain()) {
			// iterate over all eliminatees, lower dimensions first, but skip dimension zero
			if (dim != 0) {
				final boolean useCostEstimation = true;
				if (useCostEstimation) {
					final ArrayIndexBasedCostEstimation costs = computeCostEstimation(eTask, tr.getImage(dim));
					if (costs.getCost2Eliminatee().getDomain().size() > 1) {
						mLogger.info("Different costs " + costs.getCost2Eliminatee());
					}
					final boolean useIndexFrequency = false;
					final int indexFrequenceyThreshold = 3;
					if (useIndexFrequency) {
						costs.getOccurrenceMaximum();
						if (costs.getOccurrenceMaximum() >= indexFrequenceyThreshold && costs.getProposedCaseSplitDoubleton() != null) {
							final Doubleton<Term> someHighestFreqPair = costs.getProposedCaseSplitDoubleton();
							final Term effectiveIndex1;
							final Term effectiveIndex2;
							final Term effectiveTerm;
							final List<TermVariable> caseSplitEliminatees = new ArrayList<>();
							{
								final Map<Term, Term> substitutionMapping = new HashMap<>();
								final List<Term> definitions = new ArrayList<>();
								final Term index1 = someHighestFreqPair.getOneElement();
								if (!Collections.disjoint(eTask.getEliminatees(), Arrays.asList(index1.getFreeVars()))) {
									final TermVariable rep1 = mMgdScript.constructFreshTermVariable("caseSplit", index1.getSort());
									caseSplitEliminatees.add(rep1);
									effectiveIndex1 = rep1;
									substitutionMapping.put(index1, effectiveIndex1);
									definitions.add(QuantifierUtils.applyDerOperator(mMgdScript.getScript(), eTask.getQuantifier(), index1, effectiveIndex1));
								} else {
									effectiveIndex1 = index1;
								}
								final Term index2 = someHighestFreqPair.getOtherElement();
								if (!Collections.disjoint(eTask.getEliminatees(), Arrays.asList(index2.getFreeVars()))) {
									final TermVariable rep2 = mMgdScript.constructFreshTermVariable("caseSplit", index2.getSort());
									caseSplitEliminatees.add(rep2);
									effectiveIndex2 = rep2;
									substitutionMapping.put(index2, effectiveIndex2);
									definitions.add(QuantifierUtils.applyDerOperator(mMgdScript.getScript(), eTask.getQuantifier(), index2, effectiveIndex2));
								} else {
									effectiveIndex2 = index2;
								}
								final Term replaced = Substitution.apply(mMgdScript, substitutionMapping, eTask.getTerm());
								effectiveTerm = QuantifierUtils.applyDualFiniteConnective(mMgdScript.getScript(),
										eTask.getQuantifier(), replaced, QuantifierUtils.applyDualFiniteConnective(
												mMgdScript.getScript(), eTask.getQuantifier(), definitions));
							}
							final Term equals = SmtUtils.binaryEquality(mMgdScript.getScript(), effectiveIndex1, effectiveIndex2);
							final Term distinct = Elim1Store.notWith1StepPush(mMgdScript.getScript(), equals);
							final Term posContext = SmtUtils.and(mMgdScript.getScript(), eTask.getContext(), equals);
							final EliminationTaskPlain posTask = new EliminationTaskPlain(eTask.getQuantifier(), eTask.getEliminatees(), effectiveTerm, posContext);
							final EliminationTaskPlain posRes = doElimAllRec(posTask);
							final Term posResTermPostprocessed = QuantifierUtils.applyDualFiniteConnective(
									mMgdScript.getScript(), eTask.getQuantifier(), posRes.getTerm(), QuantifierUtils
											.negateIfUniversal(mServices, mMgdScript, eTask.getQuantifier(), equals));

							final Term negContext = SmtUtils.and(mMgdScript.getScript(), eTask.getContext(), distinct);
							final EliminationTaskPlain negTask = new EliminationTaskPlain(eTask.getQuantifier(), eTask.getEliminatees(), effectiveTerm, negContext);
							final EliminationTaskPlain negRes = doElimAllRec(negTask);
							final Term negResTermPostprocessed = QuantifierUtils.applyDualFiniteConnective(
									mMgdScript.getScript(), eTask.getQuantifier(), negRes.getTerm(), QuantifierUtils
											.negateIfUniversal(mServices, mMgdScript, eTask.getQuantifier(), distinct));
							final HashSet<TermVariable> resEliminatees = new HashSet<>(posRes.getEliminatees());
							resEliminatees.addAll(negRes.getEliminatees());
							resEliminatees.addAll(caseSplitEliminatees);
							final Term resTerm = QuantifierUtils.applyCorrespondingFiniteConnective(mMgdScript.getScript(),
									eTask.getQuantifier(), posResTermPostprocessed, negResTermPostprocessed);
							final EliminationTaskPlain result = new EliminationTaskPlain(
									eTask.getQuantifier(), resEliminatees, resTerm, eTask.getContext());
							final EliminationTaskPlain finalResult = applyNonSddEliminations(mServices, mMgdScript, result, PqeTechniques.ALL_LOCAL);
							return finalResult;
						}

					}
					for (final Entry<Integer, TermVariable> entry : costs.getCost2Eliminatee()) {
						// split term
						final EliminationTaskPlain eTaskForVar = new EliminationTaskPlain(eTask.getQuantifier(),
								Collections.singleton(entry.getValue()), currentTerm, eTask.getContext());
						if(eTaskForVar.getEliminatees().isEmpty()) {
							mLogger.info("Eliminatee " + entry.getValue() + " vanished before elimination");
						} else {
							final EliminationTaskSimple res = eliminateOne(eTaskForVar);
							currentTerm = res.getTerm();
							newElimnatees.addAll(res.getEliminatees());
						}
					}
				} else {
					for (final TermVariable eliminatee : tr.getImage(dim)) {
						// split term
						final EliminationTaskPlain eTaskForVar = new EliminationTaskPlain(eTask.getQuantifier(),
								Collections.singleton(eliminatee), currentTerm, eTask.getContext());
						if(eTaskForVar.getEliminatees().isEmpty()) {
							mLogger.info("Eliminatee " + eliminatee + " vanished before elimination");
						} else {
							final EliminationTaskSimple res = eliminateOne(eTaskForVar);
							currentTerm = res.getTerm();
							newElimnatees.addAll(res.getEliminatees());
						}

					}
				}

			}
		}
		final Set<TermVariable> resultingEliminatees = new LinkedHashSet<>(newElimnatees);
		resultingEliminatees.addAll(eTask.getEliminatees());
		final EliminationTaskPlain preliminaryResult = new EliminationTaskPlain(eTask.getQuantifier(),
				resultingEliminatees, currentTerm, null);
		final EliminationTaskPlain finalResult = applyNonSddEliminations(mServices, mMgdScript, preliminaryResult,
				PqeTechniques.ALL_LOCAL);
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start of recursive call " + thisRecursiveCallNumber + ": " + printVarInfo(tr)
					+ " End of recursive call: " + printVarInfo(classifyEliminatees(finalResult.getEliminatees()))
					+ " and "
					+ QuantifierUtils.getCorrespondingFiniteJuncts(finalResult.getQuantifier(), finalResult.getTerm()).length
					+ " xjuncts.");
		}
		return finalResult;
	}

	private ArrayIndexBasedCostEstimation computeCostEstimation(final EliminationTaskPlain eTask,
			final Set<TermVariable> eliminatees) throws AssertionError {
		final int quantifier = eTask.getQuantifier();
		final Term polarizedContext;
		if (quantifier == QuantifiedFormula.EXISTS) {
			polarizedContext = eTask.getContext();
		} else if (quantifier == QuantifiedFormula.FORALL) {
			polarizedContext = SmtUtils.not(mMgdScript.getScript(), eTask.getContext());
		} else {
			throw new AssertionError("unknown quantifier");
		}
		final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<>();
		final ArrayIndexEqualityManager aiem = new ArrayIndexEqualityManager(tver, polarizedContext, quantifier,
						mLogger, mMgdScript);
		final ArrayIndexBasedCostEstimation costs = new ArrayIndexBasedCostEstimation(mMgdScript.getScript(),
				aiem, eliminatees, eTask.getTerm(), eTask.getEliminatees());
		aiem.unlockSolver();
		return costs;
	}

	private EliminationTaskPlain eliminateOne(final EliminationTaskPlain eTaskForVar) throws ElimStorePlainException {
		final TermVariable eliminatee = eTaskForVar.getEliminatees().iterator().next();
		final Set<TermVariable> newElimnateesForVar = new LinkedHashSet<>();
		final Term[] correspondingJunctiveNormalForm;
		final Term dualJunctWithoutEliminatee;
		{
			final Pair<Term[], Term> split = split(eTaskForVar.getQuantifier(), eliminatee, eTaskForVar.getTerm());
			correspondingJunctiveNormalForm = split.getFirst();
			dualJunctWithoutEliminatee = split.getSecond();
		}
		final Term additionalContext = QuantifierUtils.negateIfUniversal(mServices, mMgdScript,
				eTaskForVar.getQuantifier(), dualJunctWithoutEliminatee);
		final Term parentContext = SmtUtils.and(mMgdScript.getScript(), eTaskForVar.getContext(), additionalContext);
		final Term[] resultingCorrespondingJuncts = new Term[correspondingJunctiveNormalForm.length];
		for (int i = 0; i < correspondingJunctiveNormalForm.length; i++) {
			final Term correspondingJunct = correspondingJunctiveNormalForm[i];
			if (!Arrays.asList(correspondingJunct.getFreeVars()).contains(eliminatee)) {
				// ignore correspondingJuncts that do not contain eliminatee
				resultingCorrespondingJuncts[i] = correspondingJunctiveNormalForm[i];
			} else {
				Term context;
				final boolean addSiblingContext = true;
				if (addSiblingContext) {
					context = addSiblingContext(mServices, mMgdScript, eTaskForVar.getQuantifier(),
							resultingCorrespondingJuncts, correspondingJunctiveNormalForm, i, parentContext);
				} else {
					context = parentContext;
				}
				final EliminationTaskSimple res = doElimOneRec(
						new EliminationTaskPlain(eTaskForVar.getQuantifier(),
								Collections.singleton(eliminatee), correspondingJunct, context));
				newElimnateesForVar.addAll(res.getEliminatees());
				resultingCorrespondingJuncts[i] = res.getTerm();
			}
		}
		final boolean pushContextInside = true;
		final Term preliminaryResult;
		if (pushContextInside) {
			preliminaryResult = compose(dualJunctWithoutEliminatee, eTaskForVar.getQuantifier(),
					Arrays.asList(resultingCorrespondingJuncts));
		} else {
			final Term resultingCorrespondingJunction = QuantifierUtils.applyCorrespondingFiniteConnective(
					mMgdScript.getScript(), eTaskForVar.getQuantifier(), Arrays.asList(resultingCorrespondingJuncts));
			preliminaryResult = QuantifierUtils.applyDualFiniteConnective(mMgdScript.getScript(),
					eTaskForVar.getQuantifier(), resultingCorrespondingJunction, dualJunctWithoutEliminatee);
		}
		final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mMgdScript, preliminaryResult,
				eTaskForVar.getContext(), mServices,
				mSimplificationTechnique);
		mLogger.info(esr.buildSizeReductionMessage());
		final Term simplifiedResult = esr.getSimplifiedTerm();
		final EliminationTaskPlain res = new EliminationTaskPlain(eTaskForVar.getQuantifier(),
				newElimnateesForVar, simplifiedResult, eTaskForVar.getContext());
		return res;
	}

	private Term addSiblingContext(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final int quantifier, final Term[] resultingCorrespondingJuncts,
			final Term[] correspondingJunctiveNormalForm, final int pos, final Term parentContext) {
		final ArrayList<Term> contextConjuncts = new ArrayList<>();
		contextConjuncts.add(parentContext);
		for (int i = 0; i < pos; i++) {
			contextConjuncts.add(QuantifierUtils.negateIfExistential(services, mgdScript, quantifier,
					resultingCorrespondingJuncts[i]));
		}
		for (int i = pos + 1; i < correspondingJunctiveNormalForm.length; i++) {
			contextConjuncts.add(QuantifierUtils.negateIfExistential(services, mgdScript, quantifier,
					correspondingJunctiveNormalForm[i]));
		}
		return SmtUtils.and(mgdScript.getScript(), contextConjuncts);
	}

	private Term compose(final Term dualJunct, final int quantifier, final List<Term> correspondingJuncts) {
		final Term correspondingJunction = QuantifierUtils.applyCorrespondingFiniteConnective(mMgdScript.getScript(),
				quantifier, correspondingJuncts);
		final Term result = QuantifierUtils.applyDualFiniteConnective(mMgdScript.getScript(), quantifier, dualJunct,
				correspondingJunction);
		return result;
	}

	private Pair<Term[], Term> split(final int quantifier, final TermVariable eliminatee, final Term term) {
		final List<Term> dualJunctsWithEliminatee = new ArrayList<>();
		final List<Term> dualJunctsWithoutEliminatee = new ArrayList<>();
		final Term[] dualJuncts = QuantifierUtils.getDualFiniteJuncts(quantifier, term);
		for (final Term xjunct : dualJuncts) {
			if (Arrays.asList(xjunct.getFreeVars()).contains(eliminatee)) {
				dualJunctsWithEliminatee.add(xjunct);
			} else {
				dualJunctsWithoutEliminatee.add(xjunct);
			}
		}
		final Term dualJunctionWithElimantee = QuantifierUtils.applyDualFiniteConnective(mMgdScript.getScript(),
				quantifier, dualJunctsWithEliminatee);
		final Term dualJunctionWithoutElimantee = QuantifierUtils.applyDualFiniteConnective(mMgdScript.getScript(),
				quantifier, dualJunctsWithoutEliminatee);
		final Term correspondingJunction;
		// 20190324 Matthias: We probably have to take care for equality terms
		// that allow us to apply DER. These terms have to be moved to the lowest level.
		if (TRANSFORM_TO_XNF_ON_SPLIT) {
			final Term correspondingJunctiveNormalForm = QuantifierUtils.transformToXnf(mServices, mMgdScript.getScript(),
					quantifier, mMgdScript, dualJunctionWithElimantee,
					XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION);
			correspondingJunction = correspondingJunctiveNormalForm;
		} else {
			correspondingJunction = dualJunctionWithElimantee;
		}
		final Term[] correspodingJuncts = QuantifierUtils.getCorrespondingFiniteJuncts(quantifier, correspondingJunction);
		return new Pair<Term[], Term>(correspodingJuncts, dualJunctionWithoutElimantee);
	}

	private String printVarInfo(final TreeHashRelation<Integer, TermVariable> tr) {
		final StringBuilder sb = new StringBuilder();
		for (final Integer dim : tr.getDomain()) {
			sb.append(tr.getImage(dim).size() + " dim-" + dim + " vars, ");
		}
		return sb.toString();
	}

	private void pushTaskOnStack(final EliminationTaskSimple eTask, final Stack<EliminationTaskSimple> taskStack) {
		final Term term = eTask.getTerm();
		final Term[] disjuncts = QuantifierUtils.getCorrespondingFiniteJuncts(eTask.getQuantifier(), term);
		if (disjuncts.length == 1) {
			taskStack.push(eTask);
		} else {
			for (final Term disjunct : disjuncts) {
				taskStack.push(new EliminationTaskSimple(eTask.getQuantifier(), eTask.getEliminatees(), disjunct));
			}
		}
	}

	public static EliminationTaskPlain applyNonSddEliminations(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final EliminationTaskPlain eTask, final PqeTechniques techniques)
			throws ElimStorePlainException {
		final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), eTask.getQuantifier(),
				eTask.getEliminatees(), eTask.getTerm());
		final Term pushed = QuantifierPusher.eliminate(services, mgdScript, true, techniques,
				SimplificationTechnique.SIMPLIFY_DDA, quantified);

		final Term pnf = new PrenexNormalForm(mgdScript).transform(pushed);
		final QuantifierSequence qs = new QuantifierSequence(mgdScript, pnf);
		final Term matrix = qs.getInnerTerm();
		final List<QuantifiedVariables> qvs = qs.getQuantifierBlocks();

		final Set<TermVariable> eliminatees1;
		if (qvs.isEmpty()) {
			eliminatees1 = Collections.emptySet();
		} else if (qvs.size() == 1) {
			eliminatees1 = qvs.get(0).getVariables();
			if (qvs.get(0).getQuantifier() != eTask.getQuantifier()) {
				throw new ElimStorePlainException("alternation not yet supported");
			}
		} else if (qvs.size() > 1) {
			throw new ElimStorePlainException("alternation not yet supported: " + pnf);
		} else {
			throw new AssertionError();
		}
		return new EliminationTaskPlain(eTask.getQuantifier(), eliminatees1, matrix, eTask.getContext());
	}

	private LinkedHashSet<TermVariable> getArrayTvSmallDimensionsFirst(final TreeHashRelation<Integer, TermVariable> tr) {
		final LinkedHashSet<TermVariable> result = new LinkedHashSet<>();
		for (final Integer dim : tr.getDomain()) {
			if (dim != 0) {
				result.addAll(tr.getImage(dim));
			}
		}
		return result;
	}

	/**
	 * Given a set of {@link TermVariables} a_1,...,a_n, let dim(a_i) be the "array
	 * dimension" of variable a_i. Returns a tree relation that contains (dim(a_i),
	 * a_i) for all i\in{1,...,n}.
	 */
	private static TreeHashRelation<Integer, TermVariable> classifyEliminatees(final Collection<TermVariable> eliminatees) {
		final TreeHashRelation<Integer, TermVariable> tr = new TreeHashRelation<>();
		for (final TermVariable eliminatee : eliminatees) {
			final MultiDimensionalSort mds = new MultiDimensionalSort(eliminatee.getSort());
			tr.addPair(mds.getDimension(), eliminatee);
		}
		return tr;
	}


	private static boolean maxSizeIncrease(final TreeHashRelation<Integer, TermVariable> tr1, final TreeHashRelation<Integer, TermVariable> tr2) {
		if (tr2.isEmpty()) {
			return false;
		}
		final int tr1max = tr1.descendingDomain().first();
		final int tr2max = tr2.descendingDomain().first();
		final int max = Math.max(tr1max, tr2max);
		final Set<TermVariable> maxElemsTr1 = tr1.getImage(max);
		final Set<TermVariable> maxElemsTr2 = tr2.getImage(max);
		if (maxElemsTr1 == null) {
			assert maxElemsTr2 != null;
			return true;
		}
		if (maxElemsTr2 == null) {
			assert maxElemsTr1 != null;
			return false;
		}
		return maxElemsTr2.size() > maxElemsTr1.size();

	}

	public static class ElimStorePlainException extends Exception {
		private static final long serialVersionUID = 7719170889993834143L;
		public static final String NON_TOP_LEVEL_DER = "DER that is not on top-level";
		public static final String CAPTURED_INDEX = "Subterm of an index is captued by an inner quantifier";
		private final String mMessage;
		private final TermVariable mEliminatee;

		public ElimStorePlainException(final String message) {
			super(message);
			mEliminatee = null;
			mMessage = message;
		}

		@Override
		public String getMessage() {
			return mMessage;
		}


	}

}
