/*
 * Copyright (C) 2020 Jonas Werner (wernerj@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE accelerated interpolation library .
 *
 * The ULTIMATE framework is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE framework is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE accelerated interpolation library . If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PDR library , or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE accelerated interpolation library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.lib.acceleratedinterpolation;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Transforms a given counterexample to a meta trace by replacing loops with their transitive closure.
 *
 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            Type of transition.
 */
public class MetaTraceTransformer<L extends IIcfgTransition<?>> {
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final List<L> mCounterexample;
	private final IPredicateUnifier mPredUnifier;
	private final IUltimateServiceProvider mServices;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final CfgSmtToolkit mToolkit;
	private final Map<IIcfgCallTransition<?>, IPredicate> mCallPred;

	/**
	 * Determine how to construct the meta-trace.
	 *
	 * @author Jonas Werner (wernerj@informatik.uni-freiburg.de)
	 *
	 */
	public enum MetaTraceApplicationMethod {
		ONLY_AT_FIRST_LOOP_ENTRY, ON_EACH_LOOP_ENTRY, INVARIANT
	}

	/**
	 * Transforms given meta trace interpolants to inductive trace interpolants
	 *
	 * @param logger
	 *            A {@link ILogger}
	 * @param script
	 *            A {@link ManagedScript}
	 * @param counterexample
	 *            A possible counterexample trace.
	 * @param predUnifier
	 *            A {@link PredicateUnifier}
	 * @param services
	 *            {@link IUltimateServiceProvider}
	 * @param predTransformer
	 *            A {@link PredicateTransformer}
	 * @param toolkit
	 *            A {@link CfgSmtToolkit}
	 */
	public MetaTraceTransformer(final ILogger logger, final ManagedScript script, final List<L> counterexample,
			final IPredicateUnifier predUnifier, final IUltimateServiceProvider services,
			final PredicateTransformer<Term, IPredicate, TransFormula> predTransformer, final CfgSmtToolkit toolkit) {
		mLogger = logger;
		mScript = script;
		mServices = services;
		mCounterexample = counterexample;
		mPredUnifier = predUnifier;
		mPredTransformer = predTransformer;
		mToolkit = toolkit;
		mCallPred = new HashMap<>();
	}

	/**
	 * Given meta trace interpolants yield inductive interpolants for an error trace
	 *
	 * @param preds
	 *            A set of {@link IPredicate}
	 * @param accelerations
	 *            Accelerations for loops in the trace.
	 * @param loopSizes
	 *            The sizes of each loop, eg, where in the trace do they begin and where end.
	 * @param metaTraceApplicationMethod
	 *            Which {@link MetaTraceApplicationMethod} is used.
	 * @return Inductive interpolants as {@link IPredicate}
	 */
	public IPredicate[] getInductiveLoopInterpolants(final IPredicate[] preds,
			final Map<IcfgLocation, List<UnmodifiableTransFormula>> accelerations,
			final Map<IcfgLocation, Pair<Integer, Integer>> loopSizes,
			final MetaTraceApplicationMethod metaTraceApplicationMethod) {

		final MetaTraceApplicationMethod mtam = metaTraceApplicationMethod;
		IPredicate[] actualInterpolants = new IPredicate[mCounterexample.size() - 1];
		int cnt = 0;
		for (int i = 0; i < actualInterpolants.length; i++) {
			final IcfgLocation target = mCounterexample.get(i).getTarget();
			/*
			 * When the next location is a loophead, use loopaccelerations
			 */
			if (accelerations.containsKey(target)) {
				final Pair<Integer, Integer> loopSize = loopSizes.get(target);
				final List<UnmodifiableTransFormula> loopAccelerations = new ArrayList<>(accelerations.get(target));

				final List<Term> loopAccelerationsForEntryLocation = new ArrayList<>();
				final int maxLoopPredicates = 2 * loopAccelerations.size();
				/*
				 * In case there are multiple loop accelerations, construct post of meta trace's interpolant and
				 * corresponding loop acceleration
				 */
				Term loopAccelerationsForEntryLocationDisjunction;
				final int loopSkip = 3;
				if (loopAccelerations.size() > 1) {
					int currentPredCounter = cnt;
					int currentIterationCounter = 0;
					while (currentPredCounter < maxLoopPredicates + cnt) {
						final IPredicate loopEntryInterpolantMetaTrace = preds[currentPredCounter];
						final UnmodifiableTransFormula loopAccelerationForCorrespondingLoop =
								loopAccelerations.get(currentIterationCounter);
						final Term postInterpolantLoopacceleration = mPredTransformer.strongestPostcondition(
								loopEntryInterpolantMetaTrace, loopAccelerationForCorrespondingLoop);
						loopAccelerationsForEntryLocation.add(postInterpolantLoopacceleration);
						currentIterationCounter++;
						currentPredCounter = currentPredCounter + loopSkip;
					}
					loopAccelerationsForEntryLocationDisjunction =
							SmtUtils.and(mScript.getScript(), loopAccelerationsForEntryLocation);
				} else {
					final IPredicate loopEntryInterpolantMetaTrace = preds[cnt];
					final UnmodifiableTransFormula loopAccelerationForCorrespondingLoop = loopAccelerations.get(0);
					final Term postInterpolantLoopacceleration = mPredTransformer.strongestPostcondition(
							loopEntryInterpolantMetaTrace, loopAccelerationForCorrespondingLoop);
					loopAccelerationsForEntryLocationDisjunction = postInterpolantLoopacceleration;
				}
				cnt = cnt + maxLoopPredicates - 1;
				loopAccelerationsForEntryLocationDisjunction = SmtUtils.simplify(mScript,
						loopAccelerationsForEntryLocationDisjunction, mServices, SimplificationTechnique.SIMPLIFY_DDA);

				final IPredicate interpolantPred =
						mPredUnifier.getOrConstructPredicate(loopAccelerationsForEntryLocationDisjunction);
				actualInterpolants[i] = interpolantPred;
				i++;
				final Integer loopEndPoint = i + loopSize.getSecond() - loopSize.getFirst();
				/*
				 * Because the meta trace interpolants are too few, we need to post through the whole loop to get an
				 * inductive interpolant sequence
				 */
				switch (mtam) {
				case ONLY_AT_FIRST_LOOP_ENTRY:
					actualInterpolants = getInductiveFirstEntryOnlyPost(actualInterpolants, i, loopEndPoint);
					break;
				case INVARIANT:
					actualInterpolants = getInductiveInvariant(actualInterpolants, i, loopEndPoint);
					break;
				default:
					throw new UnsupportedOperationException();
				}
				i = loopEndPoint - 1;
			} else {
				final IPredicate prevInterpol;
				/*
				 * post does not work well with false, there are instances where the interpolant on the loopexit in the
				 * meta trace is false, this, however, may not always be inductive.
				 */
				if (SmtUtils.isFalseLiteral(preds[cnt].getFormula()) && i != 0) {
					final IPredicate tmpPrevInterpol = actualInterpolants[i - 1];
					final Term post = mPredTransformer.strongestPostcondition(tmpPrevInterpol,
							mCounterexample.get(i).getTransformula());
					prevInterpol = mPredUnifier.getOrConstructPredicate(post);
				} else {
					prevInterpol = preds[cnt];
				}
				actualInterpolants[i] = prevInterpol;
			}
			cnt++;
		}
		return actualInterpolants;
	}

	private IPredicate[] getInductiveFirstEntryOnlyIterativePredTransformer(final IPredicate[] currentPreds,
			final Integer start, final Integer end, final IPredicate precondition, final IPredicate postcondition) {
		final List<L> loopTrace = mCounterexample.subList(start, end);
		final NestedWord<L> nestedWordLoopTrace = TraceCheckUtils.toNestedWord(loopTrace);
		final DefaultTransFormulas<L> rtf = new DefaultTransFormulas<>(nestedWordLoopTrace, precondition, postcondition,
				Collections.emptySortedMap(), mToolkit.getOldVarsAssignmentCache(), false);
		final IterativePredicateTransformer<L> itp = new IterativePredicateTransformer<>(
				mPredUnifier.getPredicateFactory(), mScript, mToolkit.getModifiableGlobalsTable(), mServices,
				nestedWordLoopTrace, precondition, postcondition, Collections.emptySortedMap(),
				mPredUnifier.getTruePredicate(), SimplificationTechnique.SIMPLIFY_DDA,
				XnfConversionTechnique.BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION, mToolkit.getSymbolTable());
		final List<IPredicate> loopInterpols =
				itp.computeStrongestPostconditionSequence(rtf, Collections.emptyList()).getPredicates();
		int j = start + 1;
		currentPreds[start] = precondition;
		for (int i = 0; i < loopInterpols.size(); i++) {
			currentPreds[j] = loopInterpols.get(i);
			j++;
		}
		currentPreds[end] = postcondition;
		return currentPreds;
	}

	/**
	 * Apply the disjunction of looppath predicates only to the first loophead, then post until loopexit.
	 *
	 * @param currentPreds
	 * @param start
	 * @param end
	 * @return
	 */
	private IPredicate[] getInductiveFirstEntryOnlyPost(final IPredicate[] currentPreds, final Integer start,
			final Integer end) {
		for (int j = start; j < end; j++) {
			final L l = mCounterexample.get(j);
			final IPredicate loopPostTerm = currentPreds[j - 1];
			Term postTfPred;
			final UnmodifiableTransFormula transRel = l.getTransformula();
			if (l instanceof IIcfgCallTransition<?>) {
				final IIcfgCallTransition<?> callTrans = (IIcfgCallTransition<?>) l;
				final UnmodifiableTransFormula localAss = callTrans.getLocalVarsAssignment();
				final UnmodifiableTransFormula globalAss = mToolkit.getOldVarsAssignmentCache()
						.getGlobalVarsAssignment(callTrans.getSucceedingProcedure());
				final UnmodifiableTransFormula oldAss =
						mToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(callTrans.getSucceedingProcedure());
				final Set<IProgramNonOldVar> modGlob =
						mToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(callTrans.getSucceedingProcedure());
				postTfPred =
						mPredTransformer.strongestPostconditionCall(loopPostTerm, localAss, globalAss, oldAss, modGlob);
				mCallPred.put(callTrans, mPredUnifier.getOrConstructPredicate(postTfPred));
				mLogger.debug("Dealt with Call");
			}
			if (l instanceof IIcfgReturnTransition<?, ?>) {
				final IIcfgReturnTransition<?, ?> returnTrans = (IIcfgReturnTransition<?, ?>) l;
				final UnmodifiableTransFormula oldAss =
						mToolkit.getOldVarsAssignmentCache().getOldVarsAssignment(returnTrans.getPrecedingProcedure());
				final Set<IProgramNonOldVar> modGlob =
						mToolkit.getModifiableGlobalsTable().getModifiedBoogieVars(returnTrans.getPrecedingProcedure());
				postTfPred = mPredTransformer.strongestPostconditionReturn(loopPostTerm,
						mPredUnifier.getTruePredicate(), returnTrans.getTransformula(),
						returnTrans.getCorrespondingCall().getTransformula(), oldAss, modGlob);
				mLogger.debug("Dealt with Return");
			} else {
				postTfPred = mPredTransformer.strongestPostcondition(loopPostTerm, transRel);
			}
			currentPreds[j] = mPredUnifier.getOrConstructPredicate(postTfPred);
			mLogger.debug("Generated Interpolant");
		}
		return currentPreds;

	}

	private IPredicate[] getInductiveInvariant(final IPredicate[] currentPreds, final Integer start,
			final Integer end) {
		final IPredicate invariant = currentPreds[start - 1];
		for (int j = start; j < end; j++) {
			currentPreds[j] = mPredUnifier.getOrConstructPredicate(invariant);
		}
		return currentPreds;
	}
}
