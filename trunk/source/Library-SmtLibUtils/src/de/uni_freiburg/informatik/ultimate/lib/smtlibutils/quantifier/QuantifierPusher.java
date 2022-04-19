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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Context;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierPushTermWalker;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierPushUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.QuantifierUtils.IQuantifierEliminator;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.CondisDepthCodeGenerator.CondisDepthCode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.DerScout.DerApplicability;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.DualJunctionQuantifierElimination.EliminationResult;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeHashRelation;

/**
 * Transform a Term into form where quantifier are pushed as much inwards as possible and quantifiers are eliminated via
 * local quantifier elimination techniques if possible
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class QuantifierPusher extends TermTransformer {

	public static final String NOT_DUAL_FINITE_CONNECTIVE = "not dual finite connective";

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
		 * Apply only eliminations that will not enlarge the boolean structure of the
		 * formula and that do not use an SMT-solve.
		 */
		LIGHT,
	}

	public enum FormulaClassification {
		NOT_QUANTIFIED, CORRESPONDING_FINITE_CONNECTIVE, DUAL_FINITE_CONNECTIVE, SAME_QUANTIFIER, DUAL_QUANTIFIER, ATOM,
	}

	public enum SimplificationOccasion {
		ATOM,
		AFTER_ELIMINATION_TECHNIQUES,
		AFTER_DISTRIBTIVITY;

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

	/**
	 * If set to true we check after applying distributivity if we were able to eliminate some quantified variables. If
	 * elimination failed for all variables then we return the original term without applying distributivity.
	 *
	 */
	private static final boolean EVALUATE_SUCCESS_OF_DISTRIBUTIVITY_APPLICATION = true;

	private static final boolean ELIMINATEE_SEQUENTIALIZATION = true;
	private static final boolean DER_BASED_DISTRIBUTION_PARAMETER_PRESELECTION = true;
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
			final SimplificationTechnique simplificationTechnique,
			final Set<TermVariable> bannedForDivCapture) {
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
			final SimplificationTechnique simplificationTechnique, final EliminationTask et, final IQuantifierEliminator qe) {
		final Term flattened1 =
				flattenQuantifiedFormulas(mgdScript, (QuantifiedFormula) et.toTerm(mgdScript.getScript()));
		if (!(flattened1 instanceof QuantifiedFormula)) {
			// some quantifiers could be removed for trivial reasons
			return flattened1;
		}
		final EliminationTask res1Et = new EliminationTask((QuantifiedFormula) flattened1, et.getContext());
		final EliminationTask pushed = pushDualQuantifiersInParams(services, mgdScript, applyDistributivity,
				pqeTechniques, simplificationTechnique, res1Et, qe);
		final Term pushedTerm = pushed.toTerm(mgdScript.getScript());
		if (!(pushedTerm instanceof QuantifiedFormula)) {
			// outer quantifiers removed for trivial reason after removal of inner quantifier
			return pushedTerm;
		}
		final Term flattened2 =
				flattenQuantifiedFormulas(mgdScript, (QuantifiedFormula) pushedTerm);
		if (!(flattened2 instanceof QuantifiedFormula)) {
			// some quantifiers could be removed for trivial reasons
			return flattened2;
		}
		final EliminationTask res2Et = new EliminationTask((QuantifiedFormula) flattened2, et.getContext());
		return tryToPushOverDualFiniteConnective2(services, mgdScript, applyDistributivity, pqeTechniques,
				simplificationTechnique, res2Et, qe);
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

	private static Term tryToPushOverDualFiniteConnective2(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe) {
		if (!isDualFiniteConnective(et)) {
			throw new AssertionError(NOT_DUAL_FINITE_CONNECTIVE);
		}

		// Step 1:
		// do partition
		// if you can push something, push and return
		// if you cannot push, continue
		final ParameterPartition pp = new ParameterPartition(mgdScript.getScript(), et);
		if (!pp.isIsPartitionTrivial()) {
			return pp.getTermWithPushedQuantifier();
		}

		// 2016-12-03 Matthias: plan for refactoring
		//
		// do partition
		// if you can push something, push and return
		// if you cannot push, continue
		//
		// apply sequence of eliminations
		// after each, check topmost connector
		// if 'other finite' continue
		// else push (if possible) and return
		//
		// if all elimination processed (and still 'other finite')
		// check for 'same finite' in one 'other finite'
		// if exists, distribute, apply new pusher to result
		// if less quantified return result
		// if not less quantified return term after elimination
		// if not exists return

		// TODO 20200525 Matthias:
		// (1) maybe elimination techniques should be applied before
		// and after pushing params
		// (2) Keep pushed params even if we do not (successfully) apply distribution
		// TODO 20200724 Matthias:
		// Future plan:
		// (1) apply non-expensive elimination techniques
		// (2) check if already corresponding connective
		// (3) try to push all (not only quantified) params without distributivity
		// (better with distributivity bu only for elimination guarantee)
		// include single param eliminatees
		// (4) pull corresponding quantifiers one step
		// (4a) flatten connective if necessary
		// (4b) apply iteratively if necessary
		// (5) apply all elimination techniques
		// (6) re-do until no change (probably suppported by caller of this method)
		// (7) apply distributivity
		{
			;
			final Term eliminationResult =
					applyDualJunctionEliminationTechniques(et, mgdScript, services, pqeTechniques);
			if (eliminationResult != null) {
				// something was removed
				return eliminationResult;
			}
		}
		final Term tmp = QuantifierPushUtils.pushLocalEliminateesOverCorrespondingFiniteJunction(services, mgdScript,
				applyDistributivity, pqeTechniques, simplificationTechnique, et, qe);
		if (tmp != null) {
			return tmp;
		}

		if (!applyDistributivity) {
			// nothing eliminated
			return null;
		}
		Term[] dualFiniteParams = QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), et.getTerm());
		assert dualFiniteParams.length > 1 : NOT_DUAL_FINITE_CONNECTIVE;

		if (!services.getProgressMonitorService().continueProcessing()) {
			throw new ToolchainCanceledException(QuantifierPusher.class,
					"eliminating " + et.getEliminatees().size() + " quantified variables from "
							+ dualFiniteParams.length + " " + QuantifierUtils.getNameOfDualJuncts(et.getQuantifier()));
		}

		if (et.getEliminatees().size() > 1 && ELIMINATEE_SEQUENTIALIZATION) {
			final EliminationTaskSimple etSequentialization;
			final Term seq = QuantifierPushUtils.sequentialSubsetPush(services, mgdScript, applyDistributivity,
					pqeTechniques, simplificationTechnique, et, qe);
			if (seq == null) {
				etSequentialization = et;
			} else {
				final List<TermVariable> freeVarsBefore = Arrays.asList(et.toTerm(mgdScript.getScript()).getFreeVars());
				final List<TermVariable> freeVarsAfter = Arrays.asList(seq.getFreeVars());
				if (!freeVarsBefore.containsAll(freeVarsAfter)) {
					throw new AssertionError("New free vars! Before " + freeVarsBefore + " After " + freeVarsAfter);
				}
				if (seq instanceof QuantifiedFormula) {
					etSequentialization = new EliminationTaskSimple((QuantifiedFormula) seq);
				} else {
					return seq;
				}
			}
			// return if something was eliminated
			if (!etSequentialization.getEliminatees().containsAll(et.getEliminatees())) {
				return etSequentialization.toTerm(mgdScript.getScript());
			} else {
				final Term[] correspondingFinite = QuantifierUtils.getCorrespondingFiniteJunction(
						etSequentialization.getQuantifier(), etSequentialization.getTerm());
				if (correspondingFinite.length > 1) {
					return pushOverCorrespondingFiniteConnective(mgdScript.getScript(),
							(QuantifiedFormula) etSequentialization.toTerm(mgdScript.getScript()));
				} else {
					dualFiniteParams = QuantifierUtils.getDualFiniteJunction(etSequentialization.getQuantifier(),
							etSequentialization.getTerm());
				}
			}
		}

		if (DER_BASED_DISTRIBUTION_PARAMETER_PRESELECTION) {
			final int rec = DerScout.computeRecommendation(mgdScript.getScript(), et.getEliminatees(), dualFiniteParams,
					et.getQuantifier());
			if (rec != -1) {
				final Term correspondingFinite = applyDistributivityAndPushOneStep(services, mgdScript,
						et.getQuantifier(), et.getEliminatees(), et.getContext(), dualFiniteParams, rec);
				return correspondingFinite;
			}
		}

		// 2016-12-17 Matthias TODO:
		// before applying distributivity bring each disjunct in
		// NNF (with quantifier push)
		// if afterwards some disjunct is disjunction then re-apply
		// the tryToPushOverDualFiniteConnective method
		for (int i = 0; i < dualFiniteParams.length; i++) {
			// this loop just selects some
			// correspondingFiniteJunction that we start with
			// recursive calls will take of other
			// correspondingFiniteJunctions.
			// Hence, we do not continue to iterate
			// after the first correspondingFiniteJunction
			// was found.
			// TODO: optimization: have a closer look at atoms
			// inside to determine where we apply distributivity
			// first (e.g., somewhere where some (dis)equality
			// allows us to apply DER
			if (isCorrespondingFinite(dualFiniteParams[i], et.getQuantifier())) {
				final Term correspondingFinite = applyDistributivityAndPushOneStep(services, mgdScript,
						et.getQuantifier(), et.getEliminatees(), et.getContext(), dualFiniteParams, i);
				if (!EVALUATE_SUCCESS_OF_DISTRIBUTIVITY_APPLICATION) {
					return correspondingFinite;
				}
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

	private static EliminationTask pushDualQuantifiersInParams(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask inputEt,
			final IQuantifierEliminator qe) {
		final Term[] dualFiniteParams = QuantifierUtils.getDualFiniteJunction(inputEt.getQuantifier(),
				inputEt.getTerm());
		assert dualFiniteParams.length > 1 : NOT_DUAL_FINITE_CONNECTIVE;
		final List<Term> resultDualFiniteParams = new ArrayList<Term>();
		for (int i = 0; i < dualFiniteParams.length; i++) {
			if (dualFiniteParams[i] instanceof QuantifiedFormula) {
				final Context childContext = inputEt.getContext().constructChildContextForConDis(services, mgdScript,
						((ApplicationTerm) inputEt.getTerm()).getFunction(), Arrays.asList(dualFiniteParams), i);
				final Term resultDualFiniteParamI = qe.eliminate(services, mgdScript, applyDistributivity,
						pqeTechniques, simplificationTechnique, childContext, dualFiniteParams[i]);
				resultDualFiniteParams.add(resultDualFiniteParamI);
			} else {
				resultDualFiniteParams.add(dualFiniteParams[i]);
			}
		}
		final Term dualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
				inputEt.getQuantifier(), resultDualFiniteParams);
		final EliminationTask et = new EliminationTask(inputEt.getQuantifier(), inputEt.getEliminatees(),
				dualFiniteJunction, inputEt.getContext());
		return et;
	}

	private static Term flattenQuantifiedFormulas(final ManagedScript mgdScript,
			final QuantifiedFormula quantifiedFormula) {
		final Set<String> freeVarNames =
				Arrays.stream(quantifiedFormula.getFreeVars()).map(x -> x.getName()).collect(Collectors.toSet());
		final int quantifier = quantifiedFormula.getQuantifier();
		final Term[] dualJuncts = QuantifierUtils.getDualFiniteJunction(quantifier, quantifiedFormula.getSubformula());
		final LinkedHashMap<String, TermVariable> quantifiedVariables = new LinkedHashMap<>();
		Arrays.stream(quantifiedFormula.getVariables()).forEach(x -> quantifiedVariables.put(x.getName(), x));
		final ArrayList<Term> resultDualJuncts = new ArrayList<>();
		for (final Term dualJunct : dualJuncts) {
			if (dualJunct instanceof QuantifiedFormula) {
				final QuantifiedFormula innerQuantifiedFormula = (QuantifiedFormula) dualJunct;
				if (innerQuantifiedFormula.getQuantifier() != quantifier) {
					resultDualJuncts.add(dualJunct);
				} else {
					final Map<Term, Term> substitutionMapping = new HashMap<>();
					for (final TermVariable innerVar : innerQuantifiedFormula.getVariables()) {
						TermVariable resultVar;
						if (quantifiedVariables.containsKey(innerVar.getName())
								|| freeVarNames.contains(innerVar.getName())) {
							resultVar = mgdScript.constructFreshCopy(innerVar);
							substitutionMapping.put(innerVar, resultVar);
						} else {
							resultVar = innerVar;
						}
						quantifiedVariables.put(resultVar.getName(), resultVar);
					}
					Term resultSubformula;
					if (substitutionMapping.isEmpty()) {
						resultSubformula = innerQuantifiedFormula.getSubformula();
					} else {
						resultSubformula = Substitution.apply(mgdScript, substitutionMapping,
								innerQuantifiedFormula.getSubformula());
					}
					resultDualJuncts.add(resultSubformula);
				}
			} else {
				resultDualJuncts.add(dualJunct);
			}
		}
		final Term resultDualJunction =
				QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), quantifier, resultDualJuncts);
		final Term result = SmtUtils.quantifier(mgdScript.getScript(), quantifier,
				quantifiedVariables.entrySet().stream().map(Entry::getValue).collect(Collectors.toSet()),
				resultDualJunction);
		return result;
	}









	private static EliminationTask doit(final IUltimateServiceProvider services, final ManagedScript mgdScript,
			final boolean applyDistributivity, final PqeTechniques pqeTechniques,
			final SimplificationTechnique simplificationTechnique, final EliminationTask et,
			final IQuantifierEliminator qe) {
		final Term[] dualFiniteParams = QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), et.getTerm());
		assert dualFiniteParams.length > 1 : NOT_DUAL_FINITE_CONNECTIVE;
		final List<TermVariable> remainingEliminatees = new ArrayList<>(et.getEliminatees());
		final List<TermVariable> failedEliminatees = new ArrayList<>();
		List<Term> currentDualFiniteParams = new ArrayList<>(Arrays.asList(dualFiniteParams));
		List<TermVariable> remainingEliminateesThatDoNotOccurInAllParams =
				remaningEliminateeThatDoNotOccurInAllParams(remainingEliminatees, currentDualFiniteParams);
		int i = 0;
		while (!remainingEliminateesThatDoNotOccurInAllParams.isEmpty()) {
			if (i > 20) {
				throw new AssertionError("Probably an infinite loop");
			}
			final TermVariable eliminatee = selectBestEliminatee(mgdScript.getScript(), et.getQuantifier(),
					remainingEliminateesThatDoNotOccurInAllParams, currentDualFiniteParams);
			final List<Term> finiteParamsWithEliminatee = new ArrayList<>();
			final List<Term> finiteParamsWithoutEliminatee = new ArrayList<>();
			for (final Term dualFiniteParam : currentDualFiniteParams) {
				if (Arrays.asList(dualFiniteParam.getFreeVars()).contains(eliminatee)) {
					finiteParamsWithEliminatee.add(dualFiniteParam);
				} else {
					finiteParamsWithoutEliminatee.add(dualFiniteParam);
				}
			}
			if (finiteParamsWithoutEliminatee.isEmpty()) {
				throw new AssertionError("Eliminatee cannot occur in all");
			}
			final List<TermVariable> minionEliminatees =
					determineMinionEliminatees(et.getEliminatees(), finiteParamsWithoutEliminatee);
			if (!minionEliminatees.contains(eliminatee)) {
				throw new AssertionError("Missing minion " + eliminatee);
			}
			final Term dualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
					et.getQuantifier(), finiteParamsWithEliminatee);
			// FIXME: Bin other eliminatees in context.
			final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(),
					new HashSet<>(minionEliminatees), dualFiniteJunction);
			Context context;
			{
				final Context parentContext = et.getContext();
				final List<TermVariable> nonMinionEliminatees = new ArrayList<>(remainingEliminatees);
				nonMinionEliminatees.removeAll(new HashSet<>(minionEliminatees));
				context = parentContext.constructChildContextForQuantifiedFormula(mgdScript.getScript(),
						nonMinionEliminatees);
			}
			context = context.constructChildContextForConDis(services, mgdScript,
					((ApplicationTerm) et.getTerm()).getFunction(), finiteParamsWithoutEliminatee);
			Term pushed = qe.eliminate(services, mgdScript, applyDistributivity, pqeTechniques, simplificationTechnique,
					context, quantified);
			if (pushed instanceof QuantifiedFormula) {
				final QuantifiedFormula qf = (QuantifiedFormula) pushed;
				for (final TermVariable var : Arrays.asList(qf.getVariables())) {
					if (minionEliminatees.contains(var)) {
						failedEliminatees.add(var);
					} else {
						remainingEliminatees.add(var);
					}
				}
				pushed = qf.getSubformula();
			}
			remainingEliminatees.removeAll(minionEliminatees);
			final List<Term> pushedFiniteParams =
					Arrays.asList(QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), pushed));
			currentDualFiniteParams = new ArrayList<>(pushedFiniteParams);
			currentDualFiniteParams.addAll(finiteParamsWithoutEliminatee);
			remainingEliminateesThatDoNotOccurInAllParams =
					remaningEliminateeThatDoNotOccurInAllParams(remainingEliminatees, currentDualFiniteParams);
			i++;
		}
		remainingEliminatees.addAll(failedEliminatees);
		return new EliminationTask(et.getQuantifier(), new HashSet<>(remainingEliminatees), QuantifierUtils
				.applyDualFiniteConnective(mgdScript.getScript(), et.getQuantifier(), currentDualFiniteParams),
				et.getContext());
	}


	public static TermVariable selectBestEliminatee(final Script script, final int quantifier,
			final List<TermVariable> eliminatees, final List<Term> currentDualFiniteParams) {
		if (eliminatees.size() == 1) {
			return eliminatees.iterator().next();
		}
		final Map<TermVariable, Long> score =
				computeDerApplicabilityScore(script, quantifier, eliminatees, currentDualFiniteParams);
		// final Map<TermVariable, Long> inhabitedParamTreesizes = computeTreesizeOfInhabitedParams(eliminatees,
		// currentDualFiniteParams);
		final TreeHashRelation<Long, TermVariable> tr = new TreeHashRelation<>();
		tr.reverseAddAll(score);
		final Entry<Long, HashSet<TermVariable>> best = tr.entrySet().iterator().next();
		return best.getValue().iterator().next();
	}

	private static Map<TermVariable, Long> computeDerApplicabilityScore(final Script script, final int quantifier,
			final List<TermVariable> eliminatees, final List<Term> currentDualFiniteParams) {
		final Term correspondingFiniteJunction =
				QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, currentDualFiniteParams);
		final Map<TermVariable, Long> result = new HashMap<>();
		for (final TermVariable eliminatee : eliminatees) {
			final DerApplicability da =
					new DerScout(eliminatee, script, quantifier).transduce(correspondingFiniteJunction);
			final long score = da.getWithoutDerCases().subtract(da.getWithoutVarCases()).longValueExact();
			result.put(eliminatee, score);
		}
		return result;
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
				QuantifierUtils.getCorrespondingFiniteJunction(quantifier, dualFiniteParams[i]);
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
		final Term simplifiedResult = simplify(services, mgdScript, SimplificationOccasion.AFTER_DISTRIBTIVITY, SimplificationTechnique.POLY_PAC, context, result);
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

	@Deprecated
	private Term applyOldEliminationTechniquesSequentially(final EliminationTask et, final ManagedScript mgdScript,
			final IUltimateServiceProvider services, final PqeTechniques pqeTechniques) {
		final int numberOfEliminateesBefore = et.getEliminatees().size();
		final List<XjunctPartialQuantifierElimination> elimtechniques =
				generateOldEliminationTechniques(pqeTechniques, mgdScript, services);
		final Term[] dualFiniteParams = QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), et.getTerm());
		for (final XjunctPartialQuantifierElimination technique : elimtechniques) {
			// nothing was removed in last iteration, continue with original params
			final Term[] elimResulDualFiniteParams =
					technique.tryToEliminate(et.getQuantifier(), dualFiniteParams, new HashSet<>(et.getEliminatees()));
			final Term result = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), et.getQuantifier(),
					Arrays.asList(elimResulDualFiniteParams));
			final Set<TermVariable> eliminateesAfterwards =
					PartialQuantifierElimination.constructNewEliminatees(result, et.getEliminatees());
			if (eliminateesAfterwards.isEmpty()) {
				// all were removed
				return result;
			}
			if (numberOfEliminateesBefore > eliminateesAfterwards.size()) {
				// something was removed
				final Term quantified =
						SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), eliminateesAfterwards, result);
				// if (quantified instanceof QuantifiedFormula) {
				// final QuantifiedFormula intermediate = (QuantifiedFormula) quantified;
				// return tryToPush(intermediate);
				// }
				// special case:
				// eliminatees not reported correctly, no quantifier needed
				// handle similar as empty eliminatees case
				// TODO: eliminatees should be reported correctly
				return quantified;
			}
		}
		return null;
	}

	private Term applyNewEliminationTechniquesSequentially(final EliminationTask et, final ManagedScript mgdScript,
			final IUltimateServiceProvider services, final PqeTechniques pqeTechniques) {
		final List<DualJunctionQuantifierElimination> elimtechniques =
				generateNewEliminationTechniques(pqeTechniques, mgdScript, services);
		EliminationTask currentEt = et;
		// boolean someSuccesfullElimination = false;
		// do {
		// someSuccesfullElimination = false;
		for (final DualJunctionQuantifierElimination djqe : elimtechniques) {
			final EliminationResult er = djqe.tryToEliminate(currentEt);
			if (er != null) {
				if (!er.getNewEliminatees().isEmpty()) {
					throw new AssertionError("to be implemented");
				}
				currentEt = er.getEliminationTask();
				// if (!QuantifierUtils.isDualFiniteJunction(currentEt.getQuantifier(), currentEt.getTerm())) {
				// // the boolean structure of the formula was changed
				// return currentEt.toTerm(mgdScript.getScript());
				// }
				// someSuccesfullElimination = true;
				final Term iRes = currentEt.toTerm(mgdScript.getScript());
				// if (iRes instanceof QuantifiedFormula) {
				// return tryToPush((QuantifiedFormula) iRes);
				// } else {
				return iRes;
				// }
			}
		}
		// if (someSuccesfullElimination)
		// } while(someSuccesfullElimination);
		// return currentEt.toTerm(mgdScript.getScript());
		return null;
	}

	private static Term applyNewEliminationTechniquesExhaustively(final IUltimateServiceProvider services,
			final ManagedScript mgdScript, final PqeTechniques pqeTechniques, final EliminationTask inputEt) {
		final List<DualJunctionQuantifierElimination> elimtechniques =
				generateNewEliminationTechniques(pqeTechniques, mgdScript, services);
		boolean successInLastIteration = false;
		EliminationTask currentEt = inputEt;
		int iterations = 0;
		do {
			final EliminationResult er = tryToEliminateOne(services, currentEt, elimtechniques);
			successInLastIteration = (er != null);
			if (er != null) {
				currentEt = er.integrateNewEliminatees();
				if (!currentEt.getBoundByAncestors().equals(inputEt.getBoundByAncestors())) {
					throw new AssertionError("Illegal modification of banned variables.");
				}
				final Term simplifiedTerm = simplify(services, mgdScript,
						SimplificationOccasion.AFTER_ELIMINATION_TECHNIQUES, SimplificationTechnique.POLY_PAC,
						currentEt.getContext(), er.getEliminationTask().getTerm());
				currentEt = currentEt.update(simplifiedTerm);
				if (QuantifierUtils.isCorrespondingFiniteJunction(currentEt.getQuantifier(), currentEt.getTerm())
						|| currentEt.getTerm() instanceof QuantifiedFormula) {
					return currentEt.toTerm(mgdScript.getScript());
				}
			}
			iterations++;
			if (iterations % 10 == 0) {
				final ILogger logger = services.getLoggingService().getLogger(QuantifierPusher.class);
				logger.info(String.format(
						"Run %s iterations of DualJunctionQuantifierElimination maybe there is a nontermination bug.",
						iterations));
			}
			if (!services.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(QuantifierPusher.class,
						String.format("running %s iterations of DualJunctionQuantifierElimination", iterations));
			}
		} while (successInLastIteration);
		if (currentEt == inputEt) {
			// only one non-successful iteration
			return null;
		} else {
			return currentEt.toTerm(mgdScript.getScript());
		}
	}

	private static EliminationResult tryToEliminateOne(final IUltimateServiceProvider services,
			final EliminationTask currentEt, final List<DualJunctionQuantifierElimination> elimtechniques) {
		for (final DualJunctionQuantifierElimination djqe : elimtechniques) {
			final EliminationResult er = djqe.tryToEliminate(currentEt);
			if (er != null) {
				if (er.getEliminationTask().getEliminatees().equals(currentEt.getEliminatees())) {
					services.getLoggingService().getLogger(QuantifierPusher.class).warn(
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
		switch (pqeTechniques) {
		case ALL:
			elimtechniques.add(new DualJunctionDer(mgdScript, services, false));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfIrd(mgdScript, services)));
			elimtechniques.add(new DualJunctionTir(mgdScript, services, true));
			elimtechniques.add(new DualJunctionQeAdapter2014(mgdScript, services, new XnfUpd(mgdScript, services)));
			elimtechniques.add(new DualJunctionDer(mgdScript, services, true));
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
		if (subformula instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) subformula;
			if (quantifiedSubFormula.getQuantifier() == quantifier) {
				return FormulaClassification.SAME_QUANTIFIER;
			}
			return FormulaClassification.DUAL_QUANTIFIER;
		} else if (subformula instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) subformula;
			final String correspondingFiniteConnective = SmtUtils.getCorrespondingFiniteConnective(quantifier);
			if (appTerm.getFunction().getApplicationString().equals(correspondingFiniteConnective)) {
				return FormulaClassification.CORRESPONDING_FINITE_CONNECTIVE;
			}
			final String dualFiniteConnective =
					SmtUtils.getCorrespondingFiniteConnective(SmtUtils.getOtherQuantifier(quantifier));
			if (appTerm.getFunction().getApplicationString().equals(dualFiniteConnective)) {
				return FormulaClassification.DUAL_FINITE_CONNECTIVE;
			}
			return FormulaClassification.ATOM;
		} else {
			return FormulaClassification.ATOM;
		}
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
