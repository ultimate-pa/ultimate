/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.CondisDepthCodeGenerator.CondisDepthCode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.DualJunctionQuantifierElimination.EliminationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.QuantifierUtils.IQuantifierEliminator;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Transform a Term into form where quantifier are pushed as much inwards as possible and quantifiers are eliminated via
 * local quantifier elimination techniques if possible
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierPusher extends TermTransformer {

	public enum PqeTechniques {
		/**
		 * Apply only the DER partial quantifier elimination technique
		 */
		ONLY_DER,
		/**
		 * Apply all our partial quantifier elimination techniques that can be applied locally to subterms without
		 * knowing the input term on which the quantifier elimination was called on.
		 */
		ALL_LOCAL,
		/**
		 * Same as {@link #ALL_LOCAL}, except that we do not use UPD.
		 */
		NO_UPD,
		/**
		 * Include also elimination techniques that need to know the context of subterms.
		 */
		ALL,
		/**
		 * Apply only eliminations that will not enlarge the boolean structure of the formula and that do not use an
		 * SMT-solve.
		 */
		LIGHT,
	}

	public enum FormulaClassification {
		NOT_QUANTIFIED, CORRESPONDING_FINITE_CONNECTIVE, DUAL_FINITE_CONNECTIVE, SAME_QUANTIFIER, DUAL_QUANTIFIER, ATOM,
	}

	public enum SimplificationOccasion {
		ATOM, AFTER_ELIMINATION_TECHNIQUES, AFTER_DISTRIBTIVITY;

		public String getLogString() {
			final String result;
			switch (this) {
			case AFTER_ELIMINATION_TECHNIQUES:
				result = "after elimination techniques";
				break;
			case AFTER_DISTRIBTIVITY:
				result = "after distributivity";
				break;
			case ATOM:
				result = "of atom";
				break;
			default:
				throw new AssertionError("unknown value " + this);
			}
			return result;
		}
	}

	private static final boolean DEBUG_CHECK_RESULT = false;

	private final Script mScript;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final PqeTechniques mPqeTechniques;
	private final SimplificationTechnique mSimplificationTechnique;
	private final Set<TermVariable> mBannedForDivCapture;
	/**
	 * Try to apply distributivity rules to get connectives over which we can push quantifiers. E.g. if we have a
	 * formula or the form (A && (B || C)) we cannot directly push an existential quantifier. We can apply
	 * distributivity, obtain (A && B) || (A && C) and can now push the existential quantifier one step further.
	 */
	private final boolean mApplyDistributivity;

	private QuantifierPusher(final ManagedScript script, final IUltimateServiceProvider services,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Set<TermVariable> bannedForDivCapture) {
		mServices = services;
		mMgdScript = script;
		mScript = script.getScript();
		mApplyDistributivity = applyDistributivity;
		mPqeTechniques = quantifierEliminationTechniques;
		mSimplificationTechnique = simplificationTechnique;
		mBannedForDivCapture = bannedForDivCapture;
	}

	/**
	 * @deprecated Use {@link QuantifierPushTermWalker instead}.
	 */
	@Deprecated
	public static Term eliminate(final IUltimateServiceProvider services, final ManagedScript script,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Set<TermVariable> bannedForDivCapture,
			final Term inputTerm) {
		final ILogger logger = services.getLoggingService().getLogger(QuantifierPusher.class);
		final ExtendedSimplificationResult esr1 =
				SmtUtils.simplifyWithStatistics(script, inputTerm, services, SimplificationTechnique.POLY_PAC);
		logger.info(esr1.buildSizeReductionMessage());
		final Term result = new QuantifierPusher(script, services, applyDistributivity, quantifierEliminationTechniques,
				simplificationTechnique, bannedForDivCapture).transform(esr1.getSimplifiedTerm());
		final ExtendedSimplificationResult esr2 =
				SmtUtils.simplifyWithStatistics(script, result, services, SimplificationTechnique.POLY_PAC);
		logger.info(esr2.buildSizeReductionMessage() + " " + new DAGSize().treesize(esr2.getSimplifiedTerm()));
		if (DEBUG_CHECK_RESULT) {
			final boolean tolerateUnknown = true;
			SmtUtils.checkLogicalEquivalenceForDebugging(script.getScript(), result, inputTerm, QuantifierPusher.class,
					tolerateUnknown);
		}
		return result;
	}

	public static Term eliminate(final IUltimateServiceProvider services, final ManagedScript script,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Context context, final Term inputTerm) {
		services.getLoggingService().getLogger(QuantifierPusher.class).warn("Ignoring assumption.");
		return eliminate(services, script, applyDistributivity, quantifierEliminationTechniques,
				simplificationTechnique, inputTerm);
	}

	public static Term eliminate(final IUltimateServiceProvider services, final ManagedScript script,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques,
			final SimplificationTechnique simplificationTechnique, final Term inputTerm) {
		return eliminate(services, script, applyDistributivity, quantifierEliminationTechniques,
				simplificationTechnique, Collections.emptySet(), inputTerm);
	}

	@Override
	protected void convert(final Term term) {
		FormulaClassification classification = null;
		Term currentTerm = term;
		int iterations = 0;
		while (true) {
			classification = classify(currentTerm);
			switch (classification) {
			case NOT_QUANTIFIED: {
				// let's recurse, there may be quantifiers in subformulas
				super.convert(currentTerm);
				return;
			}
			case SAME_QUANTIFIER: {
				currentTerm = QuantifierUtils.flattenQuantifiers(mScript, (QuantifiedFormula) currentTerm);
				break;
			}
			case DUAL_QUANTIFIER: {
				final EliminationTask et = new EliminationTask((QuantifiedFormula) currentTerm,
						new Context(mMgdScript.term(null, "true"), mBannedForDivCapture));
				final Term tmp = processDualQuantifier(mServices, mMgdScript, mApplyDistributivity, mPqeTechniques,
						mSimplificationTechnique, et, QuantifierPusher::eliminate);
				final FormulaClassification tmpClassification = classify(tmp);
				if (tmpClassification == FormulaClassification.DUAL_QUANTIFIER) {
					// unable to push, we have to take this subformula as result
					setResult(tmp);
					return;
				} else {
					currentTerm = tmp;
					break;
				}
			}
			case CORRESPONDING_FINITE_CONNECTIVE: {
				currentTerm = pushOverCorrespondingFiniteConnective(mScript, (QuantifiedFormula) currentTerm);
				assert currentTerm != null : "corresponding connective case must never fail";
				break;
			}
			case ATOM: {
				final Term tmp = applyEliminationToAtom(mServices, mMgdScript, mApplyDistributivity, mPqeTechniques,
						new Context(mMgdScript.term(null, "true"), mBannedForDivCapture),
						(QuantifiedFormula) currentTerm);
				if (tmp == null) {
					// no more eliminations possible
					// let's recurse, there may be quantifiers in subformulas
					final Term res = pushInner(mServices, mMgdScript, mApplyDistributivity, mPqeTechniques,
							mSimplificationTechnique, mBannedForDivCapture, (QuantifiedFormula) currentTerm,
							mMgdScript.term(null, "true"), QuantifierPusher::eliminate);
					setResult(res);
					return;
				} else {
					currentTerm = tmp;
					break;
				}
			}
			case DUAL_FINITE_CONNECTIVE: {
				final EliminationTask et = new EliminationTask((QuantifiedFormula) currentTerm,
						new Context(mMgdScript.term(null, "true"), mBannedForDivCapture));
				final Term tmp = tryToPushOverDualFiniteConnective(mServices, mMgdScript, mApplyDistributivity,
						mPqeTechniques, mSimplificationTechnique, et, QuantifierPusher::eliminate);
				if (tmp == null) {
					// no more eliminations possible
					// let's recurse, there may be quantifiers in subformulas
					final Term res = pushInner(mServices, mMgdScript, mApplyDistributivity, mPqeTechniques,
							mSimplificationTechnique, mBannedForDivCapture, (QuantifiedFormula) currentTerm,
							mMgdScript.term(null, "true"), QuantifierPusher::eliminate);
					setResult(res);
					return;
				} else {
					currentTerm = tmp;
					break;
				}
			}
			default:
				throw new AssertionError("unknown value " + classification);
			}
			iterations++;
		}
	}

	public static Term pushInner(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final Set<TermVariable> bannedForDivCapture,
			final QuantifiedFormula quantifiedFormula, final Term criticalConstraint, final IQuantifierEliminator qe) {
		final Context context = new Context(criticalConstraint, bannedForDivCapture);
		final Context childContext = context.constructChildContextForQuantifiedFormula(mgdScript.getScript(),
				Arrays.asList(quantifiedFormula.getVariables()));
		final Term subFormulaPushed = qe.eliminate(services, mgdScript, applyDistributivity, pqeTechniques,
				simplificationTechnique, childContext, quantifiedFormula.getSubformula());
		final Term res = SmtUtils.quantifier(mgdScript.getScript(), quantifiedFormula.getQuantifier(),
				new HashSet<>(Arrays.asList(quantifiedFormula.getVariables())), subFormulaPushed);
		return res;
	}

	public static Term applyEliminationToAtom(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques pqeTechniques, final Context context,
			final QuantifiedFormula quantifiedFormula) {
		final EliminationTask et = new EliminationTask(quantifiedFormula, context);
		final Term elimResult;
		if (et.getEliminatees().size() < quantifiedFormula.getVariables().length) {
			// instant removal of variables that do not occur
			elimResult = et.toTerm(mgdScript.getScript());
		} else {
			elimResult = applyDualJunctionEliminationTechniques(et, mgdScript, services, pqeTechniques);
		}
		return elimResult;
	}

	public static Term pushOverCorrespondingFiniteConnective(final Script script,
			final QuantifiedFormula quantifiedFormula) {
		assert quantifiedFormula.getSubformula() instanceof ApplicationTerm;
		final ApplicationTerm appTerm = (ApplicationTerm) quantifiedFormula.getSubformula();
		assert appTerm.getFunction().getApplicationString()
				.equals(SmtUtils.getCorrespondingFiniteConnective(quantifiedFormula.getQuantifier()));
		final Term[] oldParams = appTerm.getParameters();
		final Term[] newParams = new Term[oldParams.length];
		for (int i = 0; i < oldParams.length; i++) {
			newParams[i] = SmtUtils.quantifier(script, quantifiedFormula.getQuantifier(),
					new HashSet<>(Arrays.asList(quantifiedFormula.getVariables())), oldParams[i]);
		}
		return script.term(appTerm.getFunction().getName(), newParams);
	}

	public static Term tryToPushOverDualFiniteConnective(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe) {

		final Pair<Boolean, Term> pair = QuantifierPushUtils.preprocessDualFiniteJunction(services, mgdScript,
				applyDistributivity, pqeTechniques, simplificationTechnique, et, qe, false, true);

		if (!pair.getFirst()) {
			return pair.getSecond();
		}
		final EliminationTask preprocessedEt =
				new EliminationTask((QuantifiedFormula) pair.getSecond(), et.getContext());

		final Term eliminationResult =
				applyDualJunctionEliminationTechniques(preprocessedEt, mgdScript, services, pqeTechniques);
		if (eliminationResult != null) {
			// quantifier was at least partially removed
			return eliminationResult;
		}
		if (!applyDistributivity) {
			// we applied everything that can bring some success without applying
			// distributivity
			return null;
		}

		if (QuantifierPushUtils.OPTION_ELIMINATEE_SEQUENTIALIZATION) {
			final Term seq = QuantifierPushUtilsForSubsetPush.sequentialSubsetPush(services, mgdScript,
					applyDistributivity, pqeTechniques, simplificationTechnique, preprocessedEt, qe);
			if (seq != null) {
				return seq;
			}
		}
		return applyDistributivityAndPush(services, mgdScript, pqeTechniques, simplificationTechnique, preprocessedEt,
				qe, QuantifierPushUtils.OPTION_SCOUT_BASED_DISTRIBUTIVITY_RECOMMENDATION,
				QuantifierPushUtils.OPTION_EVALUATE_SUCCESS_OF_DISTRIBUTIVITY_APPLICATION);
	}

	private static boolean isDualFiniteConnective(final EliminationTask et) {
		if (et.getTerm() instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) et.getTerm();
			return appTerm.getFunction().getApplicationString()
					.equals(SmtUtils.getCorrespondingFiniteConnective(SmtUtils.getOtherQuantifier(et.getQuantifier())));
		} else {
			return false;
		}
	}

	public static Term applyDistributivityAndPush(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe, final boolean derBasedDistributivityParameterPreselection,
			final boolean evaluateSuccessOfDistributivityApplication) {
		final Term[] dualFiniteParams = QuantifierUtils.getDualFiniteJuncts(et.getQuantifier(), et.getTerm());
		if (dualFiniteParams.length == 1) {
			throw new AssertionError("No dual finite junction");
		}

		if (derBasedDistributivityParameterPreselection) {
			final int rec = XnfScout.computeRecommendation(mgdScript.getScript(), et.getEliminatees(), dualFiniteParams,
					et.getQuantifier());
			if (rec != -1) {
				final Term correspondingFinite = applyDistributivityAndPushOneStep(services, mgdScript,
						et.getQuantifier(), et.getEliminatees(), et.getContext(), dualFiniteParams, rec);
				return correspondingFinite;
			}
		}
		for (int i = 0; i < dualFiniteParams.length; i++) {
			// this loop just selects some
			// correspondingFiniteJunction that we start with
			// recursive calls will take of other
			// correspondingFiniteJunctions.
			// Hence, we do not continue to iterate
			// after the first correspondingFiniteJunction
			// was found.
			if (isCorrespondingFinite(dualFiniteParams[i], et.getQuantifier())) {
				final List<TermVariable> freeVars = Arrays.asList(dualFiniteParams[i].getFreeVars());
				if (DataStructureUtils.intersection(new HashSet<>(freeVars), et.getEliminatees()).isEmpty()) {
					throw new AssertionError("Useless application of distibutivity, no eliminatee involved.");
				}
				final Term correspondingFinite = applyDistributivityAndPushOneStep(services, mgdScript,
						et.getQuantifier(), et.getEliminatees(), et.getContext(), dualFiniteParams, i);
				if (!evaluateSuccessOfDistributivityApplication) {
					return correspondingFinite;
				}

				// Since this is already the distributivity method, we assume that application
				// of distributivity is desired for subsequent calls.
				final boolean applyDistributivity = true;
				final Term pushed = qe.eliminate(services, mgdScript, applyDistributivity, pqeTechniques,
						simplificationTechnique, et.getContext(), correspondingFinite);
				if (allStillQuantified(et.getEliminatees(), pushed)) {
					// we should not pay the high price for applying distributivity if we do not get
					// a formula with less quantified variales in return
					// TODO 20190323 Matthias: WARNING
					// <pre>
					// returns false negatives if the QuantifierPusher
					// would rename the quantified variables (currently not the case)
					// returns false positives if the coincidentally there is an inner quantified
					// variables that has the same name.
					// </pre>
					return null;
				} else {
					return pushed;
				}
			}
		}
		// failed to apply distributivity, return original
		return null;
	}

	private Map<TermVariable, Long> computeTreesizeOfInhabitedParams(final List<TermVariable> eliminatees,
			final List<Term> currentDualFiniteParams) {
		final List<Long> treeSize =
				currentDualFiniteParams.stream().map(x -> new DAGSize().treesize(x)).collect(Collectors.toList());
		final Map<TermVariable, Long> result = new HashMap<>();
		for (final TermVariable eliminatee : eliminatees) {
			long s = 0;
			for (int i = 0; i < currentDualFiniteParams.size(); i++) {
				if (Arrays.asList(currentDualFiniteParams.get(i).getFreeVars()).contains(eliminatee)) {
					s += treeSize.get(i);
				}
			}
			result.put(eliminatee, s);
		}
		return result;
	}

	private static List<TermVariable> remaningEliminateeThatDoNotOccurInAllParams(
			final List<TermVariable> remainingEliminatees, final List<Term> currentDualFiniteParams) {
		return remainingEliminatees.stream()
				.filter(eliminatee -> currentDualFiniteParams.stream()
						.anyMatch(param -> !Arrays.asList(param.getFreeVars()).contains(eliminatee)))
				.collect(Collectors.toList());
	}

	/**
	 * @return eliminatees that do not occur as free variable in any of the termsWithoutMasterEliminatee
	 */
	public static List<TermVariable> determineMinionEliminatees(final Collection<TermVariable> eliminatees,
			final List<Term> termsWithoutMasterEliminatee) {
		return eliminatees.stream()
				.filter(eliminatee -> termsWithoutMasterEliminatee.stream()
						.allMatch(param -> !Arrays.asList(param.getFreeVars()).contains(eliminatee)))
				.collect(Collectors.toList());
	}

	private static boolean allStillQuantified(final Set<TermVariable> eliminatees, final Term pushed) {
		final Set<Term> quantifiedFormulas = SubTermFinder.find(pushed, x -> (x instanceof QuantifiedFormula), false);
		final Set<TermVariable> allQuantifiedVars = quantifiedFormulas.stream()
				.map(x -> ((QuantifiedFormula) x).getVariables()).flatMap(Stream::of).collect(Collectors.toSet());
		return allQuantifiedVars.containsAll(eliminatees);
	}

	private static Term applyDistributivityAndPushOneStep(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final int quantifier, final Set<TermVariable> eliminatees,
			final Context context, final Term[] dualFiniteParams, final int i) {
		final Term[] correspondingFiniteParams =
				QuantifierUtils.getCorrespondingFiniteJuncts(quantifier, dualFiniteParams[i]);
		final List<Term> otherDualFiniteParams = new ArrayList<>(dualFiniteParams.length - 1);
		for (int j = 0; j < dualFiniteParams.length; j++) {
			if (j != i) {
				otherDualFiniteParams.add(dualFiniteParams[j]);
			}
		}
		final Term[] resultOuterParams = new Term[correspondingFiniteParams.length];
		int offset = 0;
		for (final Term cfp : correspondingFiniteParams) {
			final List<Term> resultInnerParams = new ArrayList<>();
			resultInnerParams.add(cfp);
			resultInnerParams.addAll(otherDualFiniteParams);
			resultOuterParams[offset] =
					QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier, resultInnerParams);
			resultOuterParams[offset] =
					SmtUtils.quantifier(mgdScript.getScript(), quantifier, eliminatees, resultOuterParams[offset]);
			offset++;
		}
		final ILogger logger = services.getLoggingService().getLogger(QuantifierPusher.class);
		if (logger.isDebugEnabled()) {
			final CondisDepthCode cdc = CondisDepthCode
					.of(QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier, dualFiniteParams));
			final String message = "Distributing " + resultOuterParams.length + " "
					+ QuantifierUtils.getNameOfCorrespondingJuncts(quantifier) + " over " + dualFiniteParams.length
					+ " " + QuantifierUtils.getNameOfDualJuncts(quantifier) + ". " + "Applying distributivity to a "
					+ cdc + " term";
			logger.info(message);
		}
		final Term result = QuantifierUtils.applyCorrespondingFiniteConnective(mgdScript.getScript(), quantifier,
				resultOuterParams);
		final Term simplifiedResult = simplify(services, mgdScript, SimplificationOccasion.AFTER_DISTRIBTIVITY,
				SimplificationTechnique.POLY_PAC, context, result);
		return simplifiedResult;
	}

	private static boolean isCorrespondingFinite(final Term term, final int quantifier) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getApplicationString()
					.equals(SmtUtils.getCorrespondingFiniteConnective(quantifier));
		}
		return false;
	}

	private static Term applyDualJunctionEliminationTechniques(final EliminationTask et, final ManagedScript mgdScript,
			final IUltimateServiceProvider services, final PqeTechniques pqeTechniques) {
		return applyNewEliminationTechniquesExhaustively(services, mgdScript, pqeTechniques, et);
	}

	private static Term applyNewEliminationTechniquesExhaustively(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final PqeTechniques pqeTechniques, final EliminationTask inputEt) {
		final List<DualJunctionQuantifierElimination> elimtechniques =
				generateNewEliminationTechniques(pqeTechniques, mgdScript, services);
		final EliminationResult er = tryToEliminateOne(services, inputEt, elimtechniques);
		if (er == null) {
			// no elimination possible
			return null;
		} else {
			EliminationTask resultEt = er.integrateNewEliminatees();
			assert (resultEt.getContext() == inputEt.getContext()) : "Illegal modification of context";
			// 20220807 Matthias: This simplification reduced the size of the formula in
			// 32 of 191 regression tests.
			final Term simplifiedTerm =
					simplify(services, mgdScript, SimplificationOccasion.AFTER_ELIMINATION_TECHNIQUES,
							SimplificationTechnique.POLY_PAC, resultEt.getContext(), resultEt.getTerm());
			resultEt = resultEt.update(simplifiedTerm);
			return resultEt.toTerm(mgdScript.getScript());
		}
	}

	private static EliminationResult tryToEliminateOne(final IUltimateServiceProvider services,
			final EliminationTask currentEt, final List<DualJunctionQuantifierElimination> elimtechniques) {
		final ILogger logger = services.getLoggingService().getLogger(QuantifierPusher.class);
		for (final DualJunctionQuantifierElimination djqe : elimtechniques) {
			final EliminationResult er = djqe.tryToEliminate(currentEt);
			if (logger.isDebugEnabled()) {
				final CondisDepthCode termCdc = CondisDepthCode.of(currentEt.getTerm());
				final CondisDepthCode contextCdc = CondisDepthCode.of(currentEt.getContext().getCriticalConstraint());
				if (er != null) {
					final Set<TermVariable> eliminated = new HashSet<>(currentEt.getEliminatees());
					eliminated.removeAll(er.getEliminationTask().getEliminatees());
					logger.debug(String.format("Applying %s to %s term with %s context. Eliminated %s Introduced %s",
							djqe.getAcronym(), termCdc, contextCdc, eliminated, er.getNewEliminatees()));
				} else {
					logger.debug(
							String.format("Applying %s to %s term with %s context. Could not eliminate any variable %s",
									djqe.getAcronym(), termCdc, contextCdc, currentEt.getEliminatees()));
				}

			}
			if (er != null) {
				if (er.getEliminationTask().getEliminatees().equals(currentEt.getEliminatees())) {
					logger.warn(
							"no eliminatee completely removed, nonetheless the elimination was considered successful");
				}
				return er;
			}
		}
		return null;
	}

	@Deprecated
	private List<DualJunctionQuantifierElimination> generateOldEliminationTechniquesWithAdapter(
			final PqeTechniques pqeTechniques, final ManagedScript mgdScript, final IUltimateServiceProvider services) {
		final List<DualJunctionQuantifierElimination> elimtechniques = new ArrayList<>();
		switch (pqeTechniques) {
		case ALL_LOCAL:
			new DualJunctionQeAdapter2014(mgdScript, services, null);
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfPlr(mgdScript, services)));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfDer(mgdScript, services)));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfIrd(mgdScript, services)));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services,
					new XnfTir(mgdScript, services, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION)));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfUpd(mgdScript, services)));
			break;
		case NO_UPD:
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfPlr(mgdScript, services)));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfDer(mgdScript, services)));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfIrd(mgdScript, services)));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services,
					new XnfTir(mgdScript, services, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION)));
			break;
		case ONLY_DER:
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfDer(mgdScript, services)));
			break;
		default:
			throw new AssertionError("unknown value " + pqeTechniques);
		}
		return elimtechniques;
	}

	private static List<DualJunctionQuantifierElimination> generateNewEliminationTechniques(
			final PqeTechniques pqeTechniques, final ManagedScript mgdScript, final IUltimateServiceProvider services) {
		final List<DualJunctionQuantifierElimination> elimtechniques = new ArrayList<>();
		final boolean useSgiElimination = false;
		if (useSgiElimination) {
			elimtechniques.add(new DualJunctionSgi(mgdScript, services));
		}
		switch (pqeTechniques) {
		case ALL:
			elimtechniques.add(new DualJunctionDer(mgdScript, services, false));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfIrd(mgdScript, services)));
			elimtechniques.add(new DualJunctionTir(mgdScript, services, true));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfUpd(mgdScript, services)));
			elimtechniques.add(new DualJunctionDml(mgdScript, services));
			final boolean useOldEliminationForDivAndMod = false;
			if (useOldEliminationForDivAndMod) {
				elimtechniques.add(new DualJunctionDer(mgdScript, services, true));
			}
			elimtechniques.add(new DualJunctionSaa(mgdScript, services, true));
			break;
		case ALL_LOCAL:
			elimtechniques.add(new DualJunctionDer(mgdScript, services, false));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfIrd(mgdScript, services)));
			elimtechniques.add(new DualJunctionTir(mgdScript, services, false));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfUpd(mgdScript, services)));
			elimtechniques.add(new DualJunctionDer(mgdScript, services, true));
			break;
		case NO_UPD:
			elimtechniques.add(new DualJunctionDer(mgdScript, services, false));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfIrd(mgdScript, services)));
			elimtechniques.add(new DualJunctionTir(mgdScript, services, false));
			elimtechniques.add(new DualJunctionDer(mgdScript, services, true));
			break;
		case ONLY_DER:
			elimtechniques.add(new DualJunctionDer(mgdScript, services, false));
			elimtechniques.add(new DualJunctionDer(mgdScript, services, true));
			break;
		case LIGHT:
			elimtechniques.add(new DualJunctionDer(mgdScript, services, false));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfIrd(mgdScript, services)));
			elimtechniques.add(new DualJunctionTir(mgdScript, services, false));
			break;
		default:
			throw new AssertionError("unknown value " + pqeTechniques);
		}
		return elimtechniques;
	}

	@Deprecated
	private static List<XjunctPartialQuantifierElimination> generateOldEliminationTechniques(
			final PqeTechniques pqeTechniques, final ManagedScript mgdScript, final IUltimateServiceProvider services) {
		final List<XjunctPartialQuantifierElimination> elimtechniques = new ArrayList<>();
		switch (pqeTechniques) {
		case ALL_LOCAL:
			elimtechniques.add(new XnfPlr(mgdScript, services));
			elimtechniques.add(new XnfDer(mgdScript, services));
			elimtechniques.add(new XnfIrd(mgdScript, services));
			elimtechniques
					.add(new XnfTir(mgdScript, services, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION));
			elimtechniques.add(new XnfUpd(mgdScript, services));
			break;
		case NO_UPD:
			elimtechniques.add(new XnfPlr(mgdScript, services));
			elimtechniques.add(new XnfDer(mgdScript, services));
			elimtechniques.add(new XnfIrd(mgdScript, services));
			elimtechniques
					.add(new XnfTir(mgdScript, services, XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION));
			break;
		case ONLY_DER:
			elimtechniques.add(new XnfDer(mgdScript, services));
			break;
		default:
			throw new AssertionError("unknown value " + pqeTechniques);
		}
		return elimtechniques;
	}

	public static FormulaClassification classify(final Term term) {
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula qf = (QuantifiedFormula) term;
			return classify(qf.getQuantifier(), qf.getSubformula());
		} else {
			return FormulaClassification.NOT_QUANTIFIED;
		}
	}

	public static FormulaClassification classify(final int quantifier, final Term subformula) {
		final FormulaClassification result;
		if (subformula instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) subformula;
			if (quantifiedSubFormula.getQuantifier() == quantifier) {
				result = FormulaClassification.SAME_QUANTIFIER;
			} else {
				result = FormulaClassification.DUAL_QUANTIFIER;
			}
		} else if (subformula instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) subformula;
			if (QuantifierUtils.isDualFiniteJunction(quantifier, appTerm)) {
				result = FormulaClassification.DUAL_FINITE_CONNECTIVE;
			} else if (QuantifierUtils.isCorrespondingFiniteJunction(quantifier, appTerm)) {
				result = FormulaClassification.CORRESPONDING_FINITE_CONNECTIVE;
			} else {
				result = FormulaClassification.ATOM;
			}
		} else {
			result = FormulaClassification.ATOM;
		}
		return result;
	}

	public static Term processDualQuantifier(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe) {
		assert et.getTerm() instanceof QuantifiedFormula;
		final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) et.getTerm();
		assert quantifiedSubFormula.getQuantifier() == SmtUtils.getOtherQuantifier(et.getQuantifier());
		final Context childContext = et.getContext().constructChildContextForQuantifiedFormula(mgdScript.getScript(),
				Arrays.asList(quantifiedSubFormula.getVariables()));
		final Term quantifiedSubFormulaPushed = qe.eliminate(services, mgdScript, applyDistributivity, pqeTechniques,
				simplificationTechnique, childContext, et.getTerm());
		final Term result = SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(),
				new HashSet<>(et.getEliminatees()), quantifiedSubFormulaPushed);
		return result;
	}

	public static Term simplify(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final SimplificationOccasion occasion, final SimplificationTechnique simplificationTechnique,
			final Context context, final Term term) {
		final ExtendedSimplificationResult esr = SmtUtils.simplifyWithStatistics(mgdScript, term,
				context.getCriticalConstraint(), services, simplificationTechnique);
		final ILogger logger = services.getLoggingService().getLogger(QuantifierPusher.class);
		if (logger.isDebugEnabled()) {
			final CondisDepthCode termCdc = CondisDepthCode.of(term);
			logger.info("Simplification " + occasion.getLogString() + " via " + String.valueOf(simplificationTechnique)
					+ ": " + esr.buildSizeReductionMessage() + " CDC code " + termCdc);
		}
		return esr.getSimplifiedTerm();
	}

	@Override
	public void convertApplicationTerm(final ApplicationTerm appTerm, final Term[] newArgs) {
		// apply local simplifications if term is "and", "or"
		// helps that we do not get terms like, e.g., ("and" true true)
		if (appTerm.getFunction().getApplicationString().equals("and")) {
			setResult(SmtUtils.and(mScript, newArgs));
		} else if (appTerm.getFunction().getApplicationString().equals("or")) {
			setResult(SmtUtils.or(mScript, newArgs));
		} else {
			super.convertApplicationTerm(appTerm, newArgs);
		}
	}

}
