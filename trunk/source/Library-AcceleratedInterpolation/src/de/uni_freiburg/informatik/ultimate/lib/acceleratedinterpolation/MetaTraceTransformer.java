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
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class MetaTraceTransformer<L extends IIcfgTransition<?>> {
	private final ILogger mLogger;
	private final ManagedScript mScript;
	private final List<L> mCounterexample;
	private final IPredicateUnifier mPredUnifier;
	private final IUltimateServiceProvider mServices;
	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredTransformer;
	private final CfgSmtToolkit mToolkit;
	private final Map<IIcfgCallTransition<?>, IPredicate> mCallPred;

	public enum MetaTraceApplicationMethod {
		ONLY_AT_FIRST_LOOP_ENTRY, ON_EACH_LOOP_ENTRY, INVARIANT
	}

	/**
	 * Transforms given meta trace interpolants to inductive trace interpolants
	 *
	 * @param logger
	 * @param script
	 * @param counterexample
	 * @param predUnifier
	 * @param services
	 * @param predTransformer
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
	 * @param accelerations
	 * @param loopSizes
	 * @param metaTraceApplicationMethod
	 * @return
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
				if (loopAccelerations.size() > 1) {
					// mtam = MetaTraceApplicationMethod.INVARIANT;
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
						currentPredCounter = currentPredCounter + 3;
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
