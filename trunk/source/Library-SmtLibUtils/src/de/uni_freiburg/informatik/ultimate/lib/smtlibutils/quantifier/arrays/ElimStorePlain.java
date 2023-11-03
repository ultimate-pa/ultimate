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

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayEqualityExplicator;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayIndexEqualityManager;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.ArrayOccurrenceAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelectOverNestedStore;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.arrays.MultiDimensionalSelectOverStoreEliminationUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.normalforms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.EliminationTask;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;

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

	public static EliminationTask applyComplexEliminationRules(final IUltimateServiceProvider services,
			final ILogger logger, final ManagedScript mgdScript, final EliminationTask eTask)
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
				eTask.getQuantifier(), eTask.getContext().getCriticalConstraint());
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
				final EliminationTask afterDer = ElimStorePlain.applyNonSddEliminations(services,
						mgdScript, new EliminationTask(eTask.getQuantifier(),
								Collections.singleton(eliminatee), termAfterDerPreprocessing, eTask.getContext()),
						PqeTechniques.ONLY_DER);
				if (!afterDer.getEliminatees().isEmpty()) {
					throw new AssertionError(" unsuccessful DER");
				}
				newAuxVars.addAll(afterDer.getEliminatees());
				return new EliminationTask(eTask.getQuantifier(), newAuxVars, afterDer.getTerm(),
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
				return new EliminationTask(eTask.getQuantifier(), newAuxVars, termAfterAntiDerPreprocessing,
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
			if(!varOccurs(eliminatee, replacedInNnf)) {
				aiem.unlockSolver();
				return new EliminationTask(eTask.getQuantifier(), newAuxVars,
						replacedInNnf, eTask.getContext());
			}
		}
		aiem.unlockSolver();
		final Term termAfterSos = sosTerm;
		final ArrayOccurrenceAnalysis aoaAfterSos = sosAoa;


		final EliminationTask eTaskForStoreElimination = new EliminationTask(
				eTask.getQuantifier(), Collections.singleton(eliminatee), termAfterSos,
				eTask.getContext());
		final EliminationTask resOfStoreElimination = new Elim1Store(mgdScript, services,
				eTask.getQuantifier()).elim1(eTaskForStoreElimination);
		// if (res.getEliminatees().contains(eliminatee)) {
		// throw new AssertionError("elimination failed");
		// }
		newAuxVars.addAll(resOfStoreElimination.getEliminatees());
		final EliminationTask eliminationResult = new EliminationTask(eTask.getQuantifier(),
				newAuxVars, resOfStoreElimination.getTerm(), eTask.getContext());
		return eliminationResult;
	}

	private static boolean varOccurs(final TermVariable var, final Term term) {
		return Arrays.stream(term.getFreeVars()).anyMatch(x -> (x == var));
	}

	private static EliminationTask applyNonSddEliminations(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final EliminationTask eTask, final PqeTechniques techniques)
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
		return new EliminationTask(eTask.getQuantifier(), eliminatees1, matrix, eTask.getContext());
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
