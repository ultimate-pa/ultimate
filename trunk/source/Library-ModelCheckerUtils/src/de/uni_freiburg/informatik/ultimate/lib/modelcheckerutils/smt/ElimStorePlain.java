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

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayIndexBasedCostEstimation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.ArrayOccurrenceAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSelectOverStoreEliminationUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeRelation;

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
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
	}

	/**
	 * Old, iterative elimination. Is sound but if we cannot eliminate all
	 * quantifiers it sometimes produces a large number of similar
	 * disjuncts/conjuncts that is too large for simplification.
	 *
	 */
	public EliminationTask elimAll(final EliminationTask eTask) {

		final Stack<EliminationTask> taskStack = new Stack<>();
		final ArrayList<Term> resultDisjuncts = new ArrayList<>();
		final Set<TermVariable> resultEliminatees = new LinkedHashSet<>();
		{
			final EliminationTask eliminationTask = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(),
					eTask.getTerm());
			pushTaskOnStack(eliminationTask, taskStack);
		}
		int numberOfRounds = 0;
		while (!taskStack.isEmpty()) {
			final EliminationTask currentETask = taskStack.pop();
			final TreeRelation<Integer, TermVariable> tr = classifyEliminatees(currentETask.getEliminatees());

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
				final EliminationTaskWithContext etwc = new EliminationTaskWithContext(currentETask.getQuantifier(),
						Collections.singleton(thisIterationEliminatee), currentETask.getTerm(), null);
				final EliminationTask ssdElimRes = new Elim1Store(mMgdScript, mServices, mSimplificationTechnique,
						eTask.getQuantifier()).elim1(etwc);
				arrayEliminatees.addAll(ssdElimRes.getEliminatees());
				// also add non-array eliminatees
				arrayEliminatees.addAll(tr.getImage(0));
				final EliminationTaskWithContext eliminationTask1 = new EliminationTaskWithContext(ssdElimRes.getQuantifier(),
						arrayEliminatees, ssdElimRes.getTerm(), null);
				final EliminationTaskWithContext eliminationTask2 = applyNonSddEliminations(mServices, mMgdScript,
						eliminationTask1, PqeTechniques.ALL_LOCAL);
				if (mLogger.isInfoEnabled()) {
					mLogger.info("Start of round: " + printVarInfo(tr) + " End of round: "
							+ printVarInfo(classifyEliminatees(eliminationTask2.getEliminatees())) + " and "
							+ QuantifierUtils.getXjunctsOuter(eTask.getQuantifier(), eliminationTask2.getTerm()).length
							+ " xjuncts.");
				}
//				assert (!maxSizeIncrease(tr, classifyEliminatees(eliminationTask2.getEliminatees()))) : "number of max-dim elements increased!";

				pushTaskOnStack(eliminationTask2, taskStack);
			}
			numberOfRounds++;
		}
		mLogger.info("Needed " + numberOfRounds + " rounds to eliminate " + eTask.getEliminatees().size()
				+ " variables, produced " + resultDisjuncts.size() + " xjuncts");
		// return term and variables that we could not eliminate
		return new EliminationTask(eTask.getQuantifier(), resultEliminatees, QuantifierUtils
				.applyCorrespondingFiniteConnective(mMgdScript.getScript(), eTask.getQuantifier(), resultDisjuncts));
	}

	/**
	 * New recursive elimination. Public method for starting the algorithm, not
	 * suitable for recursive calls.
	 */
	public EliminationTask startRecursiveElimination(final EliminationTask eTask) {
		final TreeRelation<Integer, TermVariable> tr = classifyEliminatees(eTask.getEliminatees());
		if (tr.isEmpty() || (tr.getDomain().size() == 1 && tr.getDomain().contains(0))) {
			// return immediately if we do not have quantified arrays.
			return eTask;
		}
		mRecursiveCallCounter = 0;
		final long inputSize = new DAGSize().treesize(eTask.getTerm());
		// Initially, the context is "true" (context is independent quantifier)
		final Term initialContext = mMgdScript.getScript().term("true");
		final EliminationTask result = doElimAllRec(new EliminationTaskWithContext(eTask.getQuantifier(),
				eTask.getEliminatees(), eTask.getTerm(), initialContext));
		final long outputSize = new DAGSize().treesize(result.getTerm());
		// TODO 2019-02-20 Matthias: If implementation is more matured then show this
		// output only if there was a big increase in the size of the formula.
		mLogger.info(String.format(
				"Needed %s recursive calls to eliminate %s variables, input treesize:%s, output treesize:%s",
				mRecursiveCallCounter, eTask.getEliminatees().size(), inputSize, outputSize));
		return result;
	}


	private EliminationTaskWithContext doElimOneRec(final EliminationTaskWithContext eTask) {
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
		if (split.getFirst().length != 1) {
			throw new AssertionError("no XNF");
		}
		final Term additionalContext = QuantifierUtils.negateIfUniversal(mServices, mMgdScript, eTask.getQuantifier(),
				split.getSecond());
		final Term totalContext = SmtUtils.and(mMgdScript.getScript(), eTask.getContext(), additionalContext);
		final EliminationTaskWithContext revisedInput = new EliminationTaskWithContext(eTask.getQuantifier(),
				eTask.getEliminatees(), eTask.getTerm(), totalContext);


		final EliminationTaskWithContext ssdElimRes = applyComplexEliminationRules(revisedInput);
		final EliminationTaskWithContext eliminationTask2 = applyNonSddEliminations(mServices, mMgdScript,
				ssdElimRes, PqeTechniques.ALL_LOCAL);
		final EliminationTaskWithContext resultOfRecursiveCall = doElimAllRec(eliminationTask2);
		final Term resultTerm = QuantifierUtils.applyDualFiniteConnective(mMgdScript.getScript(), eTask.getQuantifier(),
				resultOfRecursiveCall.getTerm(), split.getSecond());
		return new EliminationTaskWithContext(resultOfRecursiveCall.getQuantifier(),
				resultOfRecursiveCall.getEliminatees(), resultTerm, eTask.getContext());
	}

	private EliminationTaskWithContext applyComplexEliminationRules(final EliminationTaskWithContext eTask) {
		final TermVariable eliminatee;
		if (eTask.getEliminatees().size() != 1) {
			throw new AssertionError("need exactly one eliminatee");
		} else {
			eliminatee = eTask.getEliminatees().iterator().next();
		}
		if (!QuantifierUtils.isQuantifierFree(eTask.getTerm())) {
			throw new AssertionError("Alternating quantifiers not yet supported");
		}
		final Term polarizedContext = QuantifierUtils.negateIfUniversal(mServices, mMgdScript,
				eTask.getQuantifier(), eTask.getContext());
		final ArrayOccurrenceAnalysis aoa = new ArrayOccurrenceAnalysis(mMgdScript.getScript(), eTask.getTerm(), eliminatee);

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
						eTask.getQuantifier(), mLogger, mMgdScript);
				de = new DerPreprocessor(mServices, mMgdScript, eTask.getQuantifier(), eliminatee, eTask.getTerm(),
						aoa.getDerRelations(eTask.getQuantifier()), aiem);
				aiem.unlockSolver();
			}
			newAuxVars.addAll(de.getNewAuxVars());
			termAfterDerPreprocessing = de.getResult();
			if (de.introducedDerPossibility()) {
				// do DER
				final EliminationTaskWithContext afterDer = ElimStorePlain.applyNonSddEliminations(mServices,
						mMgdScript, new EliminationTaskWithContext(eTask.getQuantifier(),
								Collections.singleton(eliminatee), termAfterDerPreprocessing, eTask.getContext()),
						PqeTechniques.ONLY_DER);
				if (!afterDer.getEliminatees().isEmpty()) {
					throw new AssertionError(" unsuccessful DER");
				}
				newAuxVars.addAll(afterDer.getEliminatees());
				return new EliminationTaskWithContext(eTask.getQuantifier(), newAuxVars, afterDer.getTerm(),
						eTask.getContext());
			} else {
				aoaAfterDerPreprocessing = new ArrayOccurrenceAnalysis(mMgdScript.getScript(), termAfterDerPreprocessing, eliminatee);
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
			final ArrayEqualityExplicator aadk = new ArrayEqualityExplicator(mMgdScript, eTask.getQuantifier(), eliminatee,
					termAfterDerPreprocessing, aoa.getAntiDerRelations(eTask.getQuantifier()));
			termAfterAntiDerPreprocessing = aadk.getResultTerm();
			newAuxVars.addAll(aadk.getNewAuxVars());
			aoaAfterAntiDerPreprocessing = new ArrayOccurrenceAnalysis(mMgdScript.getScript(), termAfterAntiDerPreprocessing, eliminatee);
			if (!varOccurs(eliminatee, termAfterAntiDerPreprocessing)) {
				return new EliminationTaskWithContext(eTask.getQuantifier(), newAuxVars, termAfterAntiDerPreprocessing,
						eTask.getContext());
			}
		}

		// Step 3: select-over-store preprocessing
		final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<>();
		final ArrayIndexEqualityManager aiem = new ArrayIndexEqualityManager(tver, polarizedContext, eTask.getQuantifier(),
				mLogger, mMgdScript);
		ArrayOccurrenceAnalysis sosAoa = aoaAfterAntiDerPreprocessing;
		Term sosTerm = termAfterAntiDerPreprocessing;
		while (!sosAoa.getArraySelectOverStores().isEmpty()) {
			final MultiDimensionalSelectOverNestedStore mdsos = sosAoa.getArraySelectOverStores().get(0);
			final Term replaced = MultiDimensionalSelectOverStoreEliminationUtils.replace(mMgdScript, aiem,
					sosTerm, mdsos);
			final Term replacedInNnf = new NnfTransformer(mMgdScript, mServices, QuantifierHandling.KEEP).transform(replaced);
			sosTerm = replacedInNnf;
			sosAoa = new ArrayOccurrenceAnalysis(mMgdScript.getScript(), sosTerm, eliminatee);
			if(!varOccurs(eliminatee, replaced) || RETURN_AFTER_SOS) {
				aiem.unlockSolver();
				return new EliminationTaskWithContext(eTask.getQuantifier(), newAuxVars,
						replaced, eTask.getContext());
			}
		}
		aiem.unlockSolver();
		final Term termAfterSos = sosTerm;
		final ArrayOccurrenceAnalysis aoaAfterSos = sosAoa;


		final EliminationTaskWithContext eTaskForStoreElimination = new EliminationTaskWithContext(
				eTask.getQuantifier(), Collections.singleton(eliminatee), termAfterSos,
				eTask.getContext());
		final EliminationTaskWithContext resOfStoreElimination = new Elim1Store(mMgdScript, mServices,
				mSimplificationTechnique, eTask.getQuantifier()).elim1(eTaskForStoreElimination);
		// if (res.getEliminatees().contains(eliminatee)) {
		// throw new AssertionError("elimination failed");
		// }
		newAuxVars.addAll(resOfStoreElimination.getEliminatees());
		final EliminationTaskWithContext eliminationResult = new EliminationTaskWithContext(eTask.getQuantifier(),
				newAuxVars, resOfStoreElimination.getTerm(), eTask.getContext());
		return eliminationResult;
	}

	private boolean varOccurs(final TermVariable var, final Term term) {
		return Arrays.stream(term.getFreeVars()).anyMatch(x -> (x == var));
	}

	private EliminationTaskWithContext doElimAllRec(final EliminationTaskWithContext eTask) {
		mRecursiveCallCounter++;
		final int thisRecursiveCallNumber = mRecursiveCallCounter;

		final TreeRelation<Integer, TermVariable> tr = classifyEliminatees(eTask.getEliminatees());
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
								final Term replaced = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(eTask.getTerm());
								effectiveTerm = QuantifierUtils.applyDualFiniteConnective(mMgdScript.getScript(),
										eTask.getQuantifier(), replaced, QuantifierUtils.applyDualFiniteConnective(
												mMgdScript.getScript(), eTask.getQuantifier(), definitions));
							}
							final Term equals = SmtUtils.binaryEquality(mMgdScript.getScript(), effectiveIndex1, effectiveIndex2);
							final Term distinct = SmtUtils.not(mMgdScript.getScript(), equals);
							final Term posContext = SmtUtils.and(mMgdScript.getScript(), eTask.getContext(), equals);
							final EliminationTaskWithContext posTask = new EliminationTaskWithContext(eTask.getQuantifier(), eTask.getEliminatees(), effectiveTerm, posContext);
							final EliminationTaskWithContext posRes = doElimAllRec(posTask);
							final Term posResTermPostprocessed = QuantifierUtils.applyDualFiniteConnective(
									mMgdScript.getScript(), eTask.getQuantifier(), posRes.getTerm(), QuantifierUtils
											.negateIfUniversal(mServices, mMgdScript, eTask.getQuantifier(), equals));

							final Term negContext = SmtUtils.and(mMgdScript.getScript(), eTask.getContext(), distinct);
							final EliminationTaskWithContext negTask = new EliminationTaskWithContext(eTask.getQuantifier(), eTask.getEliminatees(), effectiveTerm, negContext);
							final EliminationTaskWithContext negRes = doElimAllRec(negTask);
							final Term negResTermPostprocessed = QuantifierUtils.applyDualFiniteConnective(
									mMgdScript.getScript(), eTask.getQuantifier(), negRes.getTerm(), QuantifierUtils
											.negateIfUniversal(mServices, mMgdScript, eTask.getQuantifier(), distinct));
							final HashSet<TermVariable> resEliminatees = new HashSet<>(posRes.getEliminatees());
							resEliminatees.addAll(negRes.getEliminatees());
							resEliminatees.addAll(caseSplitEliminatees);
							final Term resTerm = QuantifierUtils.applyCorrespondingFiniteConnective(mMgdScript.getScript(),
									eTask.getQuantifier(), posResTermPostprocessed, negResTermPostprocessed);
							final EliminationTaskWithContext result = new EliminationTaskWithContext(
									eTask.getQuantifier(), resEliminatees, resTerm, eTask.getContext());
							final EliminationTaskWithContext finalResult = applyNonSddEliminations(mServices, mMgdScript, result, PqeTechniques.ALL_LOCAL);
							return finalResult;
						}

					}
					for (final Entry<Integer, TermVariable> entry : costs.getCost2Eliminatee()) {
						// split term
						final EliminationTaskWithContext eTaskForVar = new EliminationTaskWithContext(eTask.getQuantifier(),
								Collections.singleton(entry.getValue()), currentTerm, eTask.getContext());
						if(eTaskForVar.getEliminatees().isEmpty()) {
							mLogger.info("Eliminatee " + entry.getValue() + " vanished before elimination");
						} else {
							final EliminationTask res = eliminateOne(eTaskForVar);
							currentTerm = res.getTerm();
							newElimnatees.addAll(res.getEliminatees());
						}
					}
				} else {
					for (final TermVariable eliminatee : tr.getImage(dim)) {
						// split term
						final EliminationTaskWithContext eTaskForVar = new EliminationTaskWithContext(eTask.getQuantifier(),
								Collections.singleton(eliminatee), currentTerm, eTask.getContext());
						if(eTaskForVar.getEliminatees().isEmpty()) {
							mLogger.info("Eliminatee " + eliminatee + " vanished before elimination");
						} else {
							final EliminationTask res = eliminateOne(eTaskForVar);
							currentTerm = res.getTerm();
							newElimnatees.addAll(res.getEliminatees());
						}

					}
				}

			}
		}
		final Set<TermVariable> resultingEliminatees = new LinkedHashSet<>(newElimnatees);
		resultingEliminatees.addAll(eTask.getEliminatees());
		final EliminationTaskWithContext preliminaryResult = new EliminationTaskWithContext(eTask.getQuantifier(),
				resultingEliminatees, currentTerm, null);
		final EliminationTaskWithContext finalResult = applyNonSddEliminations(mServices, mMgdScript, preliminaryResult,
				PqeTechniques.ALL_LOCAL);
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start of recursive call " + thisRecursiveCallNumber + ": " + printVarInfo(tr)
					+ " End of recursive call: " + printVarInfo(classifyEliminatees(finalResult.getEliminatees()))
					+ " and "
					+ QuantifierUtils.getXjunctsOuter(finalResult.getQuantifier(), finalResult.getTerm()).length
					+ " xjuncts.");
		}
		return finalResult;
	}

	private ArrayIndexBasedCostEstimation computeCostEstimation(final EliminationTaskWithContext eTask,
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

	private EliminationTask eliminateOne(final EliminationTaskWithContext eTaskForVar) {
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
				final EliminationTask res = doElimOneRec(
						new EliminationTaskWithContext(eTaskForVar.getQuantifier(),
								Collections.singleton(eliminatee), correspondingJunct, context));
				newElimnateesForVar.addAll(res.getEliminatees());
				resultingCorrespondingJuncts[i] = res.getTerm();
			}
		}
		Term currentTerm2 = compose(dualJunctWithoutEliminatee, eTaskForVar.getQuantifier(),
				Arrays.asList(resultingCorrespondingJuncts));
		final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mMgdScript, currentTerm2,
				eTaskForVar.getContext(), mServices,
				mSimplificationTechnique);
		final String sizeMessage = String.format("treesize reduction %d, result has %2.1f percent of original size",
				esr.getReductionOfTreeSize(), esr.getReductionRatioInPercent());
		mLogger.info(sizeMessage);
		currentTerm2 = esr.getSimplifiedTerm();
		final EliminationTask res = new EliminationTask(eTaskForVar.getQuantifier(), newElimnateesForVar, currentTerm2);
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
		final Term[] dualJuncts = QuantifierUtils.getXjunctsInner(quantifier, term);
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
		final Term[] correspodingJuncts = QuantifierUtils.getXjunctsOuter(quantifier, correspondingJunction);
		return new Pair<Term[], Term>(correspodingJuncts, dualJunctionWithoutElimantee);
	}

	private String printVarInfo(final TreeRelation<Integer, TermVariable> tr) {
		final StringBuilder sb = new StringBuilder();
		for (final Integer dim : tr.getDomain()) {
			sb.append(tr.getImage(dim).size() + " dim-" + dim + " vars, ");
		}
		return sb.toString();
	}

	private void pushTaskOnStack(final EliminationTask eTask, final Stack<EliminationTask> taskStack) {
		final Term term = eTask.getTerm();
		final Term[] disjuncts = QuantifierUtils.getXjunctsOuter(eTask.getQuantifier(), term);
		if (disjuncts.length == 1) {
			taskStack.push(eTask);
		} else {
			for (final Term disjunct : disjuncts) {
				taskStack.push(new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), disjunct));
			}
		}
	}

	public static EliminationTaskWithContext applyNonSddEliminations(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final EliminationTaskWithContext eTask, final PqeTechniques techniques) {
		final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), eTask.getQuantifier(),
				eTask.getEliminatees(), eTask.getTerm());
		final Term pushed = new QuantifierPusher(mgdScript, services, true, techniques).transform(quantified);

		final Term pnf = new PrenexNormalForm(mgdScript).transform(pushed);
		final QuantifierSequence qs = new QuantifierSequence(mgdScript.getScript(), pnf);
		final Term matrix = qs.getInnerTerm();
		final List<QuantifiedVariables> qvs = qs.getQuantifierBlocks();

		final Set<TermVariable> eliminatees1;
		if (qvs.isEmpty()) {
			eliminatees1 = Collections.emptySet();
		} else if (qvs.size() == 1) {
			eliminatees1 = qvs.get(0).getVariables();
			if (qvs.get(0).getQuantifier() != eTask.getQuantifier()) {
				throw new UnsupportedOperationException("alternation not yet supported");
			}
		} else if (qvs.size() > 1) {
			throw new UnsupportedOperationException("alternation not yet supported: " + pnf);
		} else {
			throw new AssertionError();
		}
		return new EliminationTaskWithContext(eTask.getQuantifier(), eliminatees1, matrix, eTask.getContext());
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

	/**
	 * Given a set of {@link TermVariables} a_1,...,a_n, let dim(a_i) be the "array
	 * dimension" of variable a_i. Returns a tree relation that contains (dim(a_i),
	 * a_i) for all i\in{1,...,n}.
	 */
	private static TreeRelation<Integer, TermVariable> classifyEliminatees(final Collection<TermVariable> eliminatees) {
		final TreeRelation<Integer, TermVariable> tr = new TreeRelation<>();
		for (final TermVariable eliminatee : eliminatees) {
			final MultiDimensionalSort mds = new MultiDimensionalSort(eliminatee.getSort());
			tr.addPair(mds.getDimension(), eliminatee);
		}
		return tr;
	}


	private static boolean maxSizeIncrease(final TreeRelation<Integer, TermVariable> tr1, final TreeRelation<Integer, TermVariable> tr2) {
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

}
