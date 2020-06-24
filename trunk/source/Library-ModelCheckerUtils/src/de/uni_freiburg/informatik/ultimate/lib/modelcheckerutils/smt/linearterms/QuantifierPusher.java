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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.CondisDepthCodeGenerator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.CondisDepthCodeGenerator.CondisDepthCode;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.DerScout;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.DerScout.DerApplicability;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.EliminationTask;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.QuantifierUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SubTermFinder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XjunctPartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfDer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfIrd;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfPlr;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfTir;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.pqe.XnfUpd;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeHashRelation;

/**
 * Transform a Term into form where quantifier are pushed as much inwards as
 * possible and quantifiers are eliminated via local quantifier elimination
 * techniques if possible
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
	}

	private enum SubformulaClassification {
		CORRESPONDING_FINITE_CONNECTIVE, DUAL_FINITE_CONNECTIVE, SAME_QUANTIFIER, DUAL_QUANTIFIER, ATOM,
	}

	/**
	 * If set to true we check after applying distributivity if we were able to eliminate some quantified variables. If
	 * elimination failed for all variables then we return the original term without applying distributivity.
	 *
	 */
	private static final boolean EVALUATE_SUCCESS_OF_DISTRIBUTIVITY_APPLICATION = true;

	private static final boolean ELIMINATEE_SEQUENTIALIZATION = true;

	private static final boolean DER_BASED_DISTRIBUTION_PARAMETER_PRESELECTION = true;

	private final Script mScript;
	private final IUltimateServiceProvider mServices;
	private final ManagedScript mMgdScript;
	private final PqeTechniques mPqeTechniques;
	/**
	 * Try to apply distributivity rules to get connectives over which we can push quantifiers. E.g. if we have a
	 * formula or the form (A && (B || C)) we cannot directly push an existential quantifier. We can apply
	 * distributivity, obtain (A && B) || (A && C) and can now push the existential quantifier one step further.
	 */
	private final boolean mApplyDistributivity;

	public QuantifierPusher(final ManagedScript script, final IUltimateServiceProvider services,
			final boolean applyDistributivity, final PqeTechniques quantifierEliminationTechniques) {
		mServices = services;
		mMgdScript = script;
		mScript = script.getScript();
		mApplyDistributivity = applyDistributivity;
		mPqeTechniques = quantifierEliminationTechniques;
	}

	@Override
	protected void convert(final Term term) {
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;
			final Term termToRecurseOn = tryToPush(quantifiedFormula);
			super.convert(termToRecurseOn);
		} else {
			super.convert(term);
		}
	}

	private Term tryToPush(QuantifiedFormula quantifiedFormula) throws AssertionError {
		SubformulaClassification classification =
				classify(quantifiedFormula.getQuantifier(), quantifiedFormula.getSubformula());
		if (classification == SubformulaClassification.DUAL_QUANTIFIER) {
			final Term dualQuantifierPushResult = processDualQuantifier(quantifiedFormula);
			if (dualQuantifierPushResult instanceof QuantifiedFormula) {
				quantifiedFormula = (QuantifiedFormula) dualQuantifierPushResult;
			} else {
				// Pushing the inner dual quantifier did not only remove that
				// quantifier but also the quantified variables bounded
				// by the outer quantifier
				return dualQuantifierPushResult;
			}
			classification = classify(quantifiedFormula.getQuantifier(), quantifiedFormula.getSubformula());
		}
		while (classification == SubformulaClassification.SAME_QUANTIFIER) {
			quantifiedFormula = processSameQuantifier(quantifiedFormula);
			classification = classify(quantifiedFormula.getQuantifier(), quantifiedFormula.getSubformula());
		}
		Term result;
		switch (classification) {
		case ATOM:
			result = applyEliminationToAtom(quantifiedFormula);
			break;
		case CORRESPONDING_FINITE_CONNECTIVE:
			result = pushOverCorrespondingFiniteConnective(quantifiedFormula);
			break;
		case DUAL_FINITE_CONNECTIVE:
			result = tryToPushOverDualFiniteConnective(quantifiedFormula);
			break;
		case DUAL_QUANTIFIER:
			// unable to push inner quantifier, hence we cannot push
			result = quantifiedFormula;
			break;
		case SAME_QUANTIFIER:
			throw new AssertionError("must have been handled above");
		default:
			throw new AssertionError("unknown value " + classification);
		}
		return result;
	}

	private Term applyEliminationToAtom(final QuantifiedFormula quantifiedFormula) {
		final Term elimResult = applyDualJunctionEliminationTechniques(new EliminationTask(
				quantifiedFormula.getQuantifier(), new HashSet<>(Arrays.asList(quantifiedFormula.getVariables())),
				quantifiedFormula.getSubformula()), mMgdScript, mServices, mPqeTechniques);
		if (elimResult == null) {
			return quantifiedFormula;
		}
		return elimResult;
	}

	private Term pushOverCorrespondingFiniteConnective(final QuantifiedFormula quantifiedFormula) {
		assert quantifiedFormula.getSubformula() instanceof ApplicationTerm;
		final ApplicationTerm appTerm = (ApplicationTerm) quantifiedFormula.getSubformula();
		assert appTerm.getFunction().getApplicationString()
				.equals(SmtUtils.getCorrespondingFiniteConnective(quantifiedFormula.getQuantifier()));
		final Term[] oldParams = appTerm.getParameters();
		final Term[] newParams = new Term[oldParams.length];
		for (int i = 0; i < oldParams.length; i++) {
			newParams[i] = SmtUtils.quantifier(mScript, quantifiedFormula.getQuantifier(),
					new HashSet<>(Arrays.asList(quantifiedFormula.getVariables())), oldParams[i]);
		}
		return mScript.term(appTerm.getFunction().getName(), newParams);
	}

	private Term tryToPushOverDualFiniteConnective(final QuantifiedFormula quantifiedFormula) {
		assert quantifiedFormula.getSubformula() instanceof ApplicationTerm;
		final ApplicationTerm appTerm = (ApplicationTerm) quantifiedFormula.getSubformula();
		assert appTerm.getFunction().getApplicationString().equals(SmtUtils
				.getCorrespondingFiniteConnective(SmtUtils.getOtherQuantifier(quantifiedFormula.getQuantifier())));

		assert quantifiedFormula.getQuantifier() == QuantifiedFormula.EXISTS
				&& appTerm.getFunction().getName().equals("and")
				|| quantifiedFormula.getQuantifier() == QuantifiedFormula.FORALL
						&& appTerm.getFunction().getName().equals("or");

		// Step 1:
		// do partition
		// if you can push something, push and return
		// if you cannot push, continue
		final ParameterPartition pp = new ParameterPartition(mScript, quantifiedFormula);
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

		final int quantifier = quantifiedFormula.getQuantifier();
		Set<TermVariable> eliminatees = new HashSet<>(Arrays.asList(quantifiedFormula.getVariables()));
		Term[] dualFiniteParams = QuantifierUtils.getXjunctsInner(quantifier, appTerm);
		// TODO 20200525 Matthias:
		// (1) maybe elimination techniques should be applied before
		// and after pushing params
		// (2) Keep pushed params even if we do not (successfully) apply distribution
		for (int i = 0; i < dualFiniteParams.length; i++) {
			if (dualFiniteParams[i] instanceof QuantifiedFormula) {
				dualFiniteParams[i] = new QuantifierPusher(mMgdScript, mServices, mApplyDistributivity, mPqeTechniques)
						.transform(dualFiniteParams[i]);
			}
		}
		// flatten params, might be necessary if some param was quantified formula
		dualFiniteParams = QuantifierUtils.getXjunctsInner(quantifier,
				QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, dualFiniteParams));
		{
			;
			final Term eliminationResult = applyDualJunctionEliminationTechniques(
					new EliminationTask(quantifier, eliminatees,
							QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, dualFiniteParams)),
					mMgdScript, mServices, mPqeTechniques);
			if (eliminationResult != null) {
				// something was removed
				return eliminationResult;
			}
		}
		if (!mApplyDistributivity) {
			// return original
			return quantifiedFormula;
		}

		if (eliminatees.size() > 1 && ELIMINATEE_SEQUENTIALIZATION) {
			final EliminationTask et = doit(quantifier, eliminatees, dualFiniteParams);
			if (et.getEliminatees().isEmpty()) {
				return et.toTerm(mScript);
			} else {
				final Term[] correspondingFinite = QuantifierUtils.getXjunctsOuter(quantifier, et.getTerm());
				if (correspondingFinite.length > 1) {
					return pushOverCorrespondingFiniteConnective((QuantifiedFormula) et.toTerm(mScript));
				} else {
					dualFiniteParams = QuantifierUtils.getXjunctsInner(quantifier, et.getTerm());
					eliminatees = et.getEliminatees();
				}
			}
		}

		if (DER_BASED_DISTRIBUTION_PARAMETER_PRESELECTION) {
			final int rec = DerScout.computeRecommendation(mScript, eliminatees, dualFiniteParams, quantifier);
			if (rec != -1) {
				final CondisDepthCode cdc = new CondisDepthCodeGenerator().transduce(appTerm);
				final ILogger logger = mServices.getLoggingService().getLogger(QuantifierPusher.class);
				logger.info("Applying distributivity to a " + cdc + " term");
				final Term correspondingFinite = applyDistributivityAndPushOneStep(quantifier, eliminatees,
						dualFiniteParams, rec);
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
			if (isCorrespondingFinite(dualFiniteParams[i], quantifier)) {
				final Term correspondingFinite = applyDistributivityAndPushOneStep(quantifier, eliminatees,
						dualFiniteParams, i);
				if (!EVALUATE_SUCCESS_OF_DISTRIBUTIVITY_APPLICATION) {
					return correspondingFinite;
				}
				final Term pushed = new QuantifierPusher(mMgdScript, mServices, mApplyDistributivity, mPqeTechniques)
						.transform(correspondingFinite);
				if (allStillQuantified(eliminatees, pushed)) {
					// we should not pay the high price for applying distributivity if we do not get
					// a formula with less quantified variales in return
					// TODO 20190323 Matthias: WARNING
					// <pre>
					// returns false negatives if the QuantifierPusher
					// would rename the quantified variables (currently not the case)
					// returns false positives if the coincidentally there is an inner quantified
					// variables that has the same name.
					// </pre>
					return quantifiedFormula;
				} else {
					return pushed;
				}
			}
		}
		// failed to apply distributivity, return original
		return quantifiedFormula;
	}

	private EliminationTask doit(final int quantifier, final Set<TermVariable> eliminatees, final Term[] dualFiniteParams) {
		final List<TermVariable> remainingEliminatees = new ArrayList<>(eliminatees);
		List<Term> currentDualFiniteParams = new ArrayList<>(Arrays.asList(dualFiniteParams));
		List<TermVariable> remainingEliminateesThatDoNotOccurInAllParams = remaningEliminateeThatDoNotOccurInAllParams(remainingEliminatees, currentDualFiniteParams);
		while (!remainingEliminateesThatDoNotOccurInAllParams.isEmpty()) {
			final TermVariable eliminatee = selectBestEliminatee(quantifier, remainingEliminateesThatDoNotOccurInAllParams, currentDualFiniteParams);
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
			final List<TermVariable> minionEliminatees = determineMinionEliminatees(eliminatees,
					finiteParamsWithoutEliminatee);
			final Term dualFiniteJunction = QuantifierUtils.applyDualFiniteConnective(mScript, quantifier,
					finiteParamsWithEliminatee);
			final Term quantified = SmtUtils.quantifier(mScript, quantifier, new HashSet<>(minionEliminatees),
					dualFiniteJunction);
			final Term pushed = new QuantifierPusher(mMgdScript, mServices, mApplyDistributivity, mPqeTechniques)
					.transform(quantified);
			remainingEliminatees.removeAll(minionEliminatees);
			final List<Term> pushedFiniteParams = Arrays.asList(QuantifierUtils.getXjunctsInner(quantifier, pushed));
			currentDualFiniteParams = new ArrayList<>(pushedFiniteParams);
			currentDualFiniteParams.addAll(finiteParamsWithoutEliminatee);
			remainingEliminateesThatDoNotOccurInAllParams = remaningEliminateeThatDoNotOccurInAllParams(remainingEliminatees, currentDualFiniteParams);
		}
		return new EliminationTask(quantifier, new HashSet<>(remainingEliminatees),
				QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, currentDualFiniteParams));
	}



	private TermVariable selectBestEliminatee(final int quantifier, final List<TermVariable> eliminatees, final List<Term> currentDualFiniteParams) {
		if (eliminatees.size() == 1) {
			return eliminatees.iterator().next();
		}
		final Map<TermVariable, Long> score = computeDerApplicabilityScore(mScript, quantifier, eliminatees,
				currentDualFiniteParams);
//		final Map<TermVariable, Long> inhabitedParamTreesizes = computeTreesizeOfInhabitedParams(eliminatees,
//				currentDualFiniteParams);
		final TreeHashRelation<Long, TermVariable> tr = new TreeHashRelation<>();
		tr.reverseAddAll(score);
		final Entry<Long, HashSet<TermVariable>> best = tr.entrySet().iterator().next();
		return best.getValue().iterator().next();
	}

	private Map<TermVariable, Long> computeDerApplicabilityScore(final Script script, final int quantifier, final List<TermVariable> eliminatees,
			final List<Term> currentDualFiniteParams) {
		final Term correspondingFiniteJunction = QuantifierUtils.applyCorrespondingFiniteConnective(script, quantifier, currentDualFiniteParams);
		final Map<TermVariable, Long> result = new HashMap<>();
		for (final TermVariable eliminatee : eliminatees) {
			final DerApplicability da = new DerScout(eliminatee, script, quantifier).transduce(correspondingFiniteJunction);
			final long score = da.getWithoutDerCases().subtract(da.getWithoutVarCases()).longValueExact();
			result.put(eliminatee, score);
		}
		return result;

	}

	private Map<TermVariable, Long> computeTreesizeOfInhabitedParams(final List<TermVariable> eliminatees,
			final List<Term> currentDualFiniteParams) {
		final List<Long> treeSize = currentDualFiniteParams.stream().map(x -> new DAGSize().treesize(x)).collect(Collectors.toList());
		final Map<TermVariable, Long> result = new HashMap<>();
		for (final TermVariable eliminatee : eliminatees) {
			long s = 0;
			for (int i=0; i<currentDualFiniteParams.size(); i++) {
				if (Arrays.asList(currentDualFiniteParams.get(i).getFreeVars()).contains(eliminatee)) {
					s += treeSize.get(i);
				}
			}
			result.put(eliminatee, s);
		}
		return result;
	}

	private List<TermVariable> remaningEliminateeThatDoNotOccurInAllParams(final List<TermVariable> remainingEliminatees,
			final List<Term> currentDualFiniteParams) {
		return remainingEliminatees.stream().filter(eliminatee -> currentDualFiniteParams.stream()
				.anyMatch(param -> !Arrays.asList(param.getFreeVars()).contains(eliminatee))).collect(Collectors.toList());
	}

	/**
	 * @return eliminatees that do not occur as free variable in any of the
	 *         termsWithoutMasterEliminatee
	 */
	private List<TermVariable> determineMinionEliminatees(final Set<TermVariable> eliminatees,
			final List<Term> termsWithoutMasterEliminatee) {
		return eliminatees.stream()
				.filter(eliminatee -> termsWithoutMasterEliminatee.stream()
						.allMatch(param -> !Arrays.asList(param.getFreeVars()).contains(eliminatee)))
				.collect(Collectors.toList());
	}

	private boolean allStillQuantified(final Set<TermVariable> eliminatees, final Term pushed) {
		final Set<Term> quantifiedFormulas =
				new SubTermFinder(x -> (x instanceof QuantifiedFormula)).findMatchingSubterms(pushed);
		final Set<TermVariable> allQuantifiedVars = quantifiedFormulas.stream()
				.map(x -> ((QuantifiedFormula) x).getVariables()).flatMap(Stream::of).collect(Collectors.toSet());
		return allQuantifiedVars.containsAll(eliminatees);
	}

	private Term applyDistributivityAndPushOneStep(final int quantifier, final Set<TermVariable> eliminatees,
			final Term[] dualFiniteParams, final int i) {
		final Term[] correspondingFiniteParams = QuantifierUtils.getXjunctsOuter(quantifier, dualFiniteParams[i]);
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
					QuantifierUtils.applyDualFiniteConnective(mScript, quantifier, resultInnerParams);
			resultOuterParams[offset] =
					SmtUtils.quantifier(mScript, quantifier, eliminatees, resultOuterParams[offset]);
			offset++;
		}
		final ILogger logger = mServices.getLoggingService().getLogger(QuantifierPusher.class);
		logger.info("Distributing " + resultOuterParams.length + " "
				+ QuantifierUtils.getNameOfCorrespondingJuncts(quantifier) + " over " + dualFiniteParams.length + " "
				+ QuantifierUtils.getNameOfDualJuncts(quantifier));
		final Term result = QuantifierUtils.applyCorrespondingFiniteConnective(mScript, quantifier, resultOuterParams);
		return result;
	}

	private boolean isCorrespondingFinite(final Term term, final int quantifier) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getApplicationString()
					.equals(SmtUtils.getCorrespondingFiniteConnective(quantifier));
		}
		return false;
	}

	private Term applyDualJunctionEliminationTechniques(final EliminationTask et, final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final PqeTechniques pqeTechniques) throws AssertionError {
		final int numberOfEliminateesBefore = et.getEliminatees().size();
		final List<XjunctPartialQuantifierElimination> elimtechniques = generateEliminationTechniques(pqeTechniques,
				mgdScript, services);
		final Term[] dualFiniteParams = QuantifierUtils.getDualFiniteJunction(et.getQuantifier(), et.getTerm());
		for (final XjunctPartialQuantifierElimination technique : elimtechniques) {
			// nothing was removed in last iteration, continue with original params
			final Term[] elimResulDualFiniteParams = technique.tryToEliminate(et.getQuantifier(), dualFiniteParams,
					new HashSet<>(et.getEliminatees()));
			final Term result = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(), et.getQuantifier(),
					Arrays.asList(elimResulDualFiniteParams));
			final Set<TermVariable> eliminateesAfterwards = PartialQuantifierElimination.constructNewEliminatees(result,
					et.getEliminatees());
			if (eliminateesAfterwards.isEmpty()) {
				// all were removed
				return result;
			}
			if (numberOfEliminateesBefore > eliminateesAfterwards.size()) {
				// something was removed
				final Term quantified = SmtUtils.quantifier(mgdScript.getScript(), et.getQuantifier(), eliminateesAfterwards,
						result);
				if (quantified instanceof QuantifiedFormula) {
					final QuantifiedFormula intermediate = (QuantifiedFormula) quantified;
					return tryToPush(intermediate);
				}
				// special case:
				// eliminatees not reported correctly, no quantifier needed
				// handle similar as empty eliminatees case
				// TODO: eliminatees should be reported correctly
				return quantified;
			}
		}
		return null;
	}

	private static List<XjunctPartialQuantifierElimination> generateEliminationTechniques(
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

	private static SubformulaClassification classify(final int quantifier, final Term subformula) {
		if (subformula instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) subformula;
			if (quantifiedSubFormula.getQuantifier() == quantifier) {
				return SubformulaClassification.SAME_QUANTIFIER;
			}
			return SubformulaClassification.DUAL_QUANTIFIER;
		} else if (subformula instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) subformula;
			final String correspondingFiniteConnective = SmtUtils.getCorrespondingFiniteConnective(quantifier);
			if (appTerm.getFunction().getApplicationString().equals(correspondingFiniteConnective)) {
				return SubformulaClassification.CORRESPONDING_FINITE_CONNECTIVE;
			}
			final String dualFiniteConnective =
					SmtUtils.getCorrespondingFiniteConnective(SmtUtils.getOtherQuantifier(quantifier));
			if (appTerm.getFunction().getApplicationString().equals(dualFiniteConnective)) {
				return SubformulaClassification.DUAL_FINITE_CONNECTIVE;
			}
			return SubformulaClassification.ATOM;
		} else {
			return SubformulaClassification.ATOM;
		}
	}

	private QuantifiedFormula processSameQuantifier(final QuantifiedFormula quantifiedFormula) {
		assert quantifiedFormula.getSubformula() instanceof QuantifiedFormula;
		final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) quantifiedFormula.getSubformula();
		assert quantifiedSubFormula.getQuantifier() == quantifiedFormula.getQuantifier();
		TermVariable[] vars;
		{
			final TermVariable[] varsOuter = quantifiedFormula.getVariables();
			final TermVariable[] varsInner = quantifiedSubFormula.getVariables();
			vars = Arrays.copyOf(varsOuter, varsOuter.length + varsInner.length);
			System.arraycopy(varsInner, 0, vars, varsOuter.length, varsInner.length);
		}
		final Term body = quantifiedSubFormula.getSubformula();
		return (QuantifiedFormula) mScript.quantifier(quantifiedFormula.getQuantifier(), vars, body);
	}

	private Term processDualQuantifier(final QuantifiedFormula quantifiedFormula) {
		assert quantifiedFormula.getSubformula() instanceof QuantifiedFormula;
		final QuantifiedFormula quantifiedSubFormula = (QuantifiedFormula) quantifiedFormula.getSubformula();
		assert quantifiedSubFormula.getQuantifier() == SmtUtils.getOtherQuantifier(quantifiedFormula.getQuantifier());
		final Term quantifiedSubFormulaPushed =
				new QuantifierPusher(mMgdScript, mServices, mApplyDistributivity, mPqeTechniques)
						.transform(quantifiedSubFormula);
		final Term result = mScript.quantifier(quantifiedFormula.getQuantifier(), quantifiedFormula.getVariables(),
				quantifiedSubFormulaPushed);
		return result;
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
