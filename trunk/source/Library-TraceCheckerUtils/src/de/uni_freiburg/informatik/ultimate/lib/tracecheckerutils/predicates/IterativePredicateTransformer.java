/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerWithPreconditionRelevanceAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerWithPreconditionRelevanceAnalysis.PrecondRelevanceResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.TraceInterpolationException.Reason;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Compute sequence of predicates via strongest post or weakest precondition along a trace.
 *
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class IterativePredicateTransformer<L extends IAction> {

	private enum BackwardSequence {
		PRE, WP
	}

	private final ModifiableGlobalsTable mModifiedGlobals;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final ManagedScript mMgdScript;

	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	private final BasicPredicateFactory mPredicateFactory;
	private final NestedWord<L> mTrace;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	protected final SortedMap<Integer, IPredicate> mPendingContexts;

	private final IPredicate mTruePredicate;

	private final IIcfgSymbolTable mSymbolTable;
	private final CfgSmtToolkit mCsToolkit;

	private static final boolean INTERPROCEDURAL_POST = true;
	private static final boolean TRANSFORM_SUMMARY_TO_CNF = true;

	/**
	 *
	 * @param truePredicate
	 *            only required if you want to compute the non-inductive wp sequence in which the call predecessor is
	 *            always the true predicate
	 */
	public IterativePredicateTransformer(final BasicPredicateFactory predicateFactory, final ManagedScript mgdScript,
			final ModifiableGlobalsTable modifiableGlobalsTable, final IUltimateServiceProvider services,
			final NestedWord<L> trace, final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final IPredicate truePredicate,
			final SimplificationTechnique simplificationTechnique, final IIcfgSymbolTable symbolTable) {
		this(predicateFactory, mgdScript, modifiableGlobalsTable, services, trace, precondition, postcondition,
				pendingContexts, truePredicate, simplificationTechnique, symbolTable, null);
	}

	public IterativePredicateTransformer(final BasicPredicateFactory predicateFactory, final ManagedScript mgdScript,
			final ModifiableGlobalsTable modifiableGlobalsTable, final IUltimateServiceProvider services,
			final NestedWord<L> trace, final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final IPredicate truePredicate,
			final SimplificationTechnique simplificationTechnique, final IIcfgSymbolTable symbolTable,
			final CfgSmtToolkit csToolkit) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(TraceCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mMgdScript = mgdScript;
		mModifiedGlobals = modifiableGlobalsTable;
		mPredicateTransformer =
				new PredicateTransformer<>(mgdScript, new TermDomainOperationProvider(mServices, mMgdScript));
		mPredicateFactory = predicateFactory;
		mTrace = trace;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPendingContexts = pendingContexts;
		mTruePredicate = truePredicate;
		mSymbolTable = symbolTable;
		mCsToolkit = csToolkit;
	}

	@FunctionalInterface
	public interface IPredicatePostprocessor {
		/**
		 * Do post processing for the predicate before the i'th action of the trace. This means especially, that if i==0
		 * we do the post processing for the precondition and if i==trace.length() we do the post processing for the
		 * postcondition.
		 */
		IPredicate postprocess(IPredicate pred, int i);
	}

	/**
	 * Compute sequence of strongest postcondition along a trace. Start with the given precondition and compute
	 * iteratively {@link IPredicate}s using the SP predicate transformer.
	 *
	 * @param nf
	 *            representation of the trace along which we compute the SP sequence
	 * @param postprocs
	 *            List of postprocessors that apply to each IPredicate after it was constructed via SP. May be empty.
	 *            TODO: If the given postcondition is null, we also compute a precondition (IPredicate before the first
	 *            {@link IAction} in the trace)
	 */
	public TracePredicates computeStrongestPostconditionSequence(
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> nf,
			final List<IPredicatePostprocessor> postprocs) {
		final IPredicate[] spSequence = new IPredicate[mTrace.length() - 1];
		final TracePredicates ipp = new TracePredicates(mPrecondition, mPostcondition, Arrays.asList(spSequence));

		final boolean computePostcondition = mPostcondition == null;
		final int positionOfLastPredicate = computePostcondition ? mTrace.length() : mTrace.length() - 1;

		IPredicate computedPostcondition = null;
		for (int i = 0; i < positionOfLastPredicate; i++) {
			final IPredicate predecessor = ipp.getPredicate(i);
			final Term spTerm;
			if (mTrace.getSymbol(i) instanceof IIcfgCallTransition<?>) {
				final IIcfgCallTransition<?> call = (IIcfgCallTransition<?>) mTrace.getSymbol(i);
				final String calledMethod = call.getSucceedingProcedure();
				final Set<IProgramNonOldVar> modifiedGlobals = mModifiedGlobals.getModifiedBoogieVars(calledMethod);
				if (mTrace.isPendingCall(i) || !INTERPROCEDURAL_POST) {
					spTerm = mPredicateTransformer.strongestPostconditionCall(predecessor, nf.getLocalVarAssignment(i),
							nf.getGlobalVarAssignment(i), nf.getOldVarAssignment(i), modifiedGlobals);
				} else {
					spTerm = mPredicateTransformer.modularPostconditionCall(predecessor, nf.getGlobalVarAssignment(i),
							modifiedGlobals);
				}
			} else if (mTrace.getSymbol(i) instanceof IIcfgReturnTransition<?, ?>) {
				final IPredicate callerPred;
				final UnmodifiableTransFormula callOldVarsAssignment;
				final UnmodifiableTransFormula callLocalVarsAssignment;
				if (mTrace.isPendingReturn(i)) {
					callerPred = mPendingContexts.get(i);
					callOldVarsAssignment = nf.getOldVarAssignment(i);
					callLocalVarsAssignment = nf.getLocalVarAssignment(i);
				} else {
					final int callPos = mTrace.getCallPosition(i);
					assert callPos >= 0 && callPos <= i : "Bad call position!";
					callerPred = ipp.getPredicate(callPos);
					callOldVarsAssignment = nf.getOldVarAssignment(callPos);
					callLocalVarsAssignment = nf.getLocalVarAssignment(callPos);
				}
				final UnmodifiableTransFormula returnTransFormula = nf.getFormulaFromNonCallPos(i);
				final String calledProcedure = mTrace.getSymbol(i).getPrecedingProcedure();
				spTerm = mPredicateTransformer.strongestPostconditionReturn(predecessor, callerPred, returnTransFormula,
						callLocalVarsAssignment, callOldVarsAssignment,
						mModifiedGlobals.getModifiedBoogieVars(calledProcedure));
			} else {
				spTerm = mPredicateTransformer.strongestPostcondition(predecessor, nf.getFormulaFromNonCallPos(i));
			}
			final IPredicate sp = constructPredicate(spTerm);
			final IPredicate postprocessed = applyPostprocessors(postprocs, i + 1, sp);
			if (i == mTrace.length() - 1) {
				computedPostcondition = postprocessed;
			} else {
				spSequence[i] = postprocessed;
			}
		}

		if (computePostcondition) {
			final TracePredicates result =
					new TracePredicates(mPrecondition, computedPostcondition, Arrays.asList(spSequence));
			return result;
		}
		return ipp;
	}

	public TracePredicates applyBackwardHoareCorePostprocessing(final TracePredicates input,
			final List<IPredicatePostprocessor> postprocs,
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rtf) {
		return new BackwardHoareCorePostprocessor(mCsToolkit, mPrecondition, mPostcondition, mLogger, mTrace,
				mPendingContexts, mPredicateFactory, rtf).applyBackwardHoareCorePostprocessing(input, postprocs);
	}

	/**
	 * Eliminate quantifiers and construct predicate.
	 */
	private IPredicate constructPredicate(final Term term) {
		final IPredicate pred = mPredicateFactory.newPredicate(term);
		return pred;
	}

	public static class QuantifierEliminationPostprocessor implements IPredicatePostprocessor {

		private final IUltimateServiceProvider mServices;
		private final ManagedScript mMgdScript;
		private final BasicPredicateFactory mPredicateFactory;
		private final SimplificationTechnique mSimplificationTechnique;

		public QuantifierEliminationPostprocessor(final IUltimateServiceProvider services,
				final ManagedScript boogie2smt, final BasicPredicateFactory predicateFactory,
				final SimplificationTechnique simplificationTechnique) {
			mServices = services;
			mMgdScript = boogie2smt;
			mPredicateFactory = predicateFactory;
			mSimplificationTechnique = simplificationTechnique;
		}

		@Override
		public IPredicate postprocess(final IPredicate pred, final int i) {
			final Term resultTerm = PartialQuantifierElimination.eliminate(mServices, mMgdScript, pred.getFormula(),
					mSimplificationTechnique);
			return mPredicateFactory.newPredicate(resultTerm);
		}
	}

	/**
	 * Compute sequence of weakest precondition along a trace. Start with the given postcondition and compute
	 * iteratively {@link IPredicate}s using the WP predicate transformer. If the given precondition is null, we also
	 * compute a precondition (IPredicate before the first {@link IAction} in the trace)
	 *
	 * @param nf
	 *            representation of the trace along which we compute the WP sequence
	 * @param postprocs
	 *            List of postprocessors that apply to each IPredicate after it was constructed via WP. May be empty.
	 *
	 * @param useTrueAsCallPredecessor
	 *            In our interprocedural setting, a return has two predecessor a linear predecessor (predicate before
	 *            return) and a hierarchical predecessor (predicate before the call). A consequence is that the weakest
	 *            precondition(s) of a return is/are not unique. The stronger the call predecessor the weaker the return
	 *            predecessor and vice versa. Only a carefully chosen compromise between both extremes ensures that the
	 *            resulting sequence is inductive. If this option is set to true, we compute the return predecessor
	 *            without any "help" from the call predecessor (i.e., under the assumption that the call predecessor is
	 *            true). If this option is set to false, the resulting sequence will be inductive. For most applications
	 *            you should pick "false".
	 *
	 * @throws TraceInterpolationException
	 *
	 */
	public TracePredicates computeWeakestPreconditionSequence(
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> nf,
			final List<IPredicatePostprocessor> postprocs, final boolean useTrueAsCallPredecessor,
			final boolean alternatingQuantifierBailout) throws TraceInterpolationException {
		return computeBackwardSequence(nf, postprocs, useTrueAsCallPredecessor, alternatingQuantifierBailout,
				BackwardSequence.WP);
	}

	public TracePredicates computePreSequence(final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> nf,
			final List<IPredicatePostprocessor> postprocs, final boolean alternatingQuantifierBailout)
			throws TraceInterpolationException {
		return computeBackwardSequence(nf, postprocs, true, alternatingQuantifierBailout, BackwardSequence.PRE);
	}

	public TracePredicates computeBackwardSequence(final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> nf,
			final List<IPredicatePostprocessor> postprocs, final boolean useTrueAsCallPredecessor,
			final boolean alternatingQuantifierBailout, final BackwardSequence bs) throws TraceInterpolationException {
		final IPredicate[] backwardSequence = new IPredicate[mTrace.length() - 1];
		final TracePredicates ipp;
		if (bs == BackwardSequence.WP) {
			ipp = new TracePredicates(mPrecondition, mPostcondition, Arrays.asList(backwardSequence));
		} else {
			ipp = new TracePredicates(mPrecondition, mPostcondition, Arrays.asList(backwardSequence));
		}

		/**
		 * Contains the predicates, which are computed during a Return with the second method, where the callerPred is
		 * computed as wp(returnerPred, summaryOfCalledProcedure).
		 */
		final Map<Integer, IPredicate> callerPredicatesComputed = new HashMap<>();

		final boolean computePrecondition = mPrecondition == null;
		final int positionOfFirstPredicate = computePrecondition ? 0 : 1;
		IPredicate computedPrecondition = null;

		for (int i = mTrace.length() - 1; i >= positionOfFirstPredicate; i--) {
			final Term backwardTerm;

			final IPredicate successorWp;
			if (bs == BackwardSequence.WP) {
				successorWp = ipp.getPredicate(i + 1);
			} else {
				successorWp = mPredicateFactory.not(ipp.getPredicate(i + 1));
			}
			if (mTrace.getSymbol(i) instanceof IIcfgCallTransition<?>) {
				if (mTrace.isPendingCall(i)) {
					final IIcfgCallTransition<?> call = (IIcfgCallTransition<?>) mTrace.getSymbol(i);
					final String calledMethod = call.getSucceedingProcedure();
					final Set<IProgramNonOldVar> modifiedGlobals = mModifiedGlobals.getModifiedBoogieVars(calledMethod);
					backwardTerm =
							mPredicateTransformer.weakestPreconditionCall(successorWp, nf.getLocalVarAssignment(i),
									nf.getGlobalVarAssignment(i), nf.getOldVarAssignment(i), modifiedGlobals);
				} else {
					// Call predecessor of non-pending calls are computed at
					// while processing the return
					assert callerPredicatesComputed.get(i) != null : "must have already been computed";
					backwardTerm = null;
				}
			} else if (mTrace.getSymbol(i) instanceof IIcfgReturnTransition<?, ?>) {
				final IPredicate callerPred;

				final UnmodifiableTransFormula oldVarAssignments;
				final UnmodifiableTransFormula callLocalVarsAssignment;

				if (mTrace.isPendingReturn(i)) {
					if (useTrueAsCallPredecessor) {
						callerPred = mTruePredicate;
					} else {
						callerPred = mPendingContexts.get(Integer.valueOf(i));
					}
					// we may get the local variable assignment (pending
					// context)
					// by requesting it at the position of the
					// pending-return.
					callLocalVarsAssignment = nf.getLocalVarAssignment(i);
					oldVarAssignments = nf.getOldVarAssignment(i);
				} else {
					final int callPos = mTrace.getCallPosition(i);
					assert callPos >= 0 && callPos <= i : "Bad call position!";
					final UnmodifiableTransFormula summary = TraceCheckUtils.computeProcedureSummary(mTrace, nf,
							callPos, i, mMgdScript, mServices, mLogger, mSimplificationTechnique, mSymbolTable,
							mModifiedGlobals, TRANSFORM_SUMMARY_TO_CNF);

					final Term preOrWpOfSummaryTerm;
					if (bs == BackwardSequence.WP) {
						preOrWpOfSummaryTerm = mPredicateTransformer.weakestPrecondition(successorWp, summary);
					} else {
						preOrWpOfSummaryTerm = SmtUtils.not(mMgdScript.getScript(),
								mPredicateTransformer.weakestPrecondition(successorWp, summary));
					}

					final IPredicate preOrWpOfSummaryPredicate = constructPredicate(preOrWpOfSummaryTerm);
					final IPredicate preOrWpOfSummary =
							applyPostprocessors(postprocs, callPos, preOrWpOfSummaryPredicate);

					if (alternatingQuantifierBailout) {
						final Term pnf = new PrenexNormalForm(mMgdScript).transform(preOrWpOfSummary.getFormula());
						if (pnf instanceof QuantifiedFormula) {
							throw new TraceInterpolationException(Reason.ALTERNATING_QUANTIFIER_BAILOUT);
						}
					}
					callerPredicatesComputed.put(callPos, preOrWpOfSummary);
					if (useTrueAsCallPredecessor) {
						callerPred = mTruePredicate;
					} else {
						callerPred = preOrWpOfSummary;
					}
					callLocalVarsAssignment = nf.getLocalVarAssignment(callPos);
					oldVarAssignments = nf.getOldVarAssignment(callPos);
				}
				final UnmodifiableTransFormula returnTf = nf.getFormulaFromNonCallPos(i);
				final IIcfgReturnTransition<?, ?> returnCB = (IIcfgReturnTransition<?, ?>) mTrace.getSymbol(i);
				final String calledMethod = returnCB.getCorrespondingCall().getSucceedingProcedure();
				final Set<IProgramNonOldVar> modifiableGlobals = mModifiedGlobals.getModifiedBoogieVars(calledMethod);
				backwardTerm = mPredicateTransformer.weakestPreconditionReturn(successorWp, callerPred, returnTf,
						callLocalVarsAssignment, oldVarAssignments, modifiableGlobals);
			} else {
				backwardTerm = mPredicateTransformer.weakestPrecondition(successorWp, nf.getFormulaFromNonCallPos(i));
			}
			final IPredicate postprocessed;
			if (mTrace.getSymbol(i) instanceof IIcfgCallTransition<?> && !mTrace.isPendingCall(i)) {
				// predicate was already constructed while processing the
				// corresponding return
				postprocessed = callerPredicatesComputed.get(i);
			} else {
				final IPredicate backwardPredicate;
				if (bs == BackwardSequence.WP) {
					backwardPredicate = constructPredicate(backwardTerm);
				} else {
					backwardPredicate = constructPredicate(SmtUtils.not(mMgdScript.getScript(), backwardTerm));
				}
				postprocessed = applyPostprocessors(postprocs, i, backwardPredicate);
			}
			if (i == 0) {
				computedPrecondition = postprocessed;
			} else {
				backwardSequence[i - 1] = postprocessed;
			}
		}
		if (computePrecondition) {
			if (bs == BackwardSequence.WP) {
				return new TracePredicates(computedPrecondition, mPostcondition, Arrays.asList(backwardSequence));
			}
			return new TracePredicates(computedPrecondition, mPostcondition, Arrays.asList(backwardSequence));
		}
		return ipp;
	}

	private static IPredicate applyPostprocessors(final List<IPredicatePostprocessor> postprocs, final int i,
			final IPredicate pred) {
		IPredicate postprocessed = pred;
		for (final IPredicatePostprocessor postproc : postprocs) {
			postprocessed = postproc.postprocess(postprocessed, i);
		}
		return postprocessed;
	}

	// /**
	// * TODO: documentation (short, refer to WP computation)
	// */
	// public TracePredicates computePreSequence(final NestedFormulas<UnmodifiableTransFormula, IPredicate> nf,
	// final List<IPredicatePostprocessor> postprocs, final boolean alternatingQuantifierBailout)
	// throws TraceInterpolationException {
	// final TracePredicates wpSequence = computeWeakestPreconditionSequence(nf, postprocs, true,
	// alternatingQuantifierBailout);
	// final IPredicate precondition = mPredicateFactory.not(wpSequence.getPrecondition());
	// final IPredicate postcondition = mPredicateFactory.not(wpSequence.getPostcondition());
	// final List<IPredicate> predicates = new ArrayList<>(wpSequence.getPredicates().size());
	// for (final IPredicate wpPredicate : wpSequence.getPredicates()) {
	// predicates.add(mPredicateFactory.not(wpPredicate));
	// }
	// return new TracePredicates(precondition, postcondition, predicates);
	// }

	public static class TraceInterpolationException extends Exception {
		private static final long serialVersionUID = -3626917726747958448L;

		public enum Reason {
			ALTERNATING_QUANTIFIER_BAILOUT
		}

		private final Reason mReason;

		public TraceInterpolationException(final Reason reason) {
			mReason = reason;
		}

		public Reason getReason() {
			return mReason;
		}

	}

	private final class BackwardHoareCorePostprocessor {
		private final CfgSmtToolkit mCsToolkit;
		private final IPredicate mPrecondition;
		private final IPredicate mPostcondition;
		private final ILogger mLogger;
		private final NestedWord<L> mTrace;
		private final SortedMap<Integer, IPredicate> mPendingContexts;
		private final BasicPredicateFactory mPredicateFactory;
		@SuppressWarnings("unused")
		private final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> mRtf;

		private int mOverallSizeReduction;
		private int mOverallUnknowns;
		private int mOverallConjuncts;
		private int mOverallPositionsWithReduction;
		private int mOverallTrivial;

		private BackwardHoareCorePostprocessor(final CfgSmtToolkit csToolkit, final IPredicate precondition,
				final IPredicate postcondition, final ILogger logger, final NestedWord<L> trace,
				final SortedMap<Integer, IPredicate> pendingContexts, final BasicPredicateFactory predicateFactory,
				final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rtf) {
			mCsToolkit = csToolkit;
			mPrecondition = precondition;
			mPostcondition = postcondition;
			mLogger = logger;
			mTrace = trace;
			mPendingContexts = pendingContexts;
			mPredicateFactory = predicateFactory;
			mRtf = rtf;
		}

		private TracePredicates applyBackwardHoareCorePostprocessing(final TracePredicates input,
				final List<IPredicatePostprocessor> postprocs) {
			mOverallSizeReduction = 0;
			mOverallUnknowns = 0;
			mOverallConjuncts = 0;
			mOverallPositionsWithReduction = 0;
			mOverallTrivial = 0;
			final List<IPredicate> predicates = new ArrayList<>();
			predicates.add(input.getPrecondition());
			predicates.addAll(input.getPredicates());
			predicates.add(input.getPostcondition());
			final HoareTripleCheckerWithPreconditionRelevanceAnalysis checker =
					new HoareTripleCheckerWithPreconditionRelevanceAnalysis(mCsToolkit, mLogger);
			try {
				// Iterate backwards up to 1, because we don't want to refine the precondition.
				for (int i = mTrace.length() - 1; i >= 1; --i) {
					final IPredicate predecessor = predicates.get(i);
					final IPredicate successor = predicates.get(i + 1);
					final List<IPredicate> predecessorConjuncts = splitConjunctively(predecessor);
					mOverallConjuncts += predecessorConjuncts.size();
					final int pos = i;
					final IAction action = mTrace.getSymbol(pos);
					switch (action) {
					case final IInternalAction internalAction: {
						if (!mTrace.isInternalPosition(pos)) {
							throw new AssertionError("not an internal action at internal position");
						}
						if (SmtUtils.isTrueLiteral(predecessor.getFormula())
								|| SmtUtils.isFalseLiteral(predecessor.getFormula())) {
							predicates.set(i, applyPostprocessors(postprocs, i, predecessor));
							mOverallTrivial++;
							continue;
						}
						final PrecondRelevanceResult checkResult =
								checker.checkInternal(predecessorConjuncts, internalAction, successor);
						final PredicateReductionResult res =
								constructReduction(postprocs, predecessorConjuncts, pos, checkResult);
						setRefinedPredicate(predicates, postprocs, predecessor, pos, res);
						break;
					}
					case final ICallAction callAction: {
						if (!mTrace.isCallPosition(pos)) {
							throw new AssertionError("not a call action at call position");
						}
						if (!mTrace.isPendingCall(pos)) {
							// for pending calls, we must not weaken the precondition, the precondition was already
							// weakened
							// when we handled the return.
//							predicates.set(i, applyPostprocessors(postprocs, i, predecessor));
							continue;
						}
						if (SmtUtils.isTrueLiteral(predecessor.getFormula())
								|| SmtUtils.isFalseLiteral(predecessor.getFormula())) {
							predicates.set(i, applyPostprocessors(postprocs, i, predecessor));
							mOverallTrivial++;
							continue;
						}

						final PrecondRelevanceResult checkResult =
								checker.checkCall(predecessorConjuncts, callAction, successor);
						final PredicateReductionResult res =
								constructReduction(postprocs, predecessorConjuncts, pos, checkResult);
						setRefinedPredicate(predicates, postprocs, predecessor, pos, res);
						break;
					}
					case final IReturnAction returnAction: {
						if (!mTrace.isReturnPosition(pos)) {
							throw new AssertionError("not a return action at return position");
						}
						IPredicate hierPre;
						final int callPos = mTrace.getCallPosition(pos);
						if (mTrace.isPendingReturn(pos)) {
							hierPre = mPendingContexts.get(pos);
						} else {
							hierPre = predicates.get(callPos);
							if (SmtUtils.isTrueLiteral(hierPre.getFormula())
									|| SmtUtils.isFalseLiteral(hierPre.getFormula())) {
								predicates.set(callPos, applyPostprocessors(postprocs, callPos, hierPre));
								mOverallTrivial++;
							} else {
								final UnmodifiableTransFormula summaryTf =
										TraceCheckUtils.computeProcedureSummary(mTrace, mRtf, callPos, pos, mMgdScript,
												mServices, mLogger, mSimplificationTechnique, mSymbolTable,
												mModifiedGlobals, TRANSFORM_SUMMARY_TO_CNF);
								final IInternalAction summary = new IInternalAction() {
									@Override
									public String getPrecedingProcedure() {
										return returnAction.getSucceedingProcedure();
									}

									@Override
									public String getSucceedingProcedure() {
										return returnAction.getSucceedingProcedure();
									}

									@Override
									public String toString() {
										return "Summary of " + mTrace.getSymbol(callPos) + " and " + returnAction;
									}

									@Override
									public UnmodifiableTransFormula getTransformula() {
										return summaryTf;
									}
								};
								final List<IPredicate> hierPreConjuncts = splitConjunctively(hierPre);
								final PrecondRelevanceResult checkResult =
										checker.checkInternal(hierPreConjuncts, summary, successor);
								final PredicateReductionResult res =
										constructReduction(postprocs, hierPreConjuncts, callPos, checkResult);
								setRefinedPredicate(predicates, postprocs, hierPre, callPos, res);
								if (res.sizeReduction() > 0) {
									hierPre = predicates.get(callPos);
								}
							}
						}
						if (SmtUtils.isTrueLiteral(predecessor.getFormula())
								|| SmtUtils.isFalseLiteral(predecessor.getFormula())) {
							predicates.set(i, applyPostprocessors(postprocs, i, predecessor));
							mOverallTrivial++;
							continue;
						}
						final PrecondRelevanceResult checkResult =
								checker.checkReturn(predecessorConjuncts, hierPre, returnAction, successor);
						final PredicateReductionResult res =
								constructReduction(postprocs, predecessorConjuncts, pos, checkResult);
						setRefinedPredicate(predicates, postprocs, predecessor, pos, res);
						break;
					}
					default:
						throw new AssertionError("Unexpected action type " + action.getClass());
					}
				}
			} finally {
				checker.releaseLock();
			}

			predicates.remove(0);
			predicates.remove(predicates.size() - 1);
			mLogger.warn(String.format(
					"Backward Hoare core postprocessing reduced overall conjuncts from %s to %s. %s IPredicates, %s allowed reduction, %s trivial, %s solver unknowns",
					mOverallConjuncts, mOverallConjuncts - mOverallSizeReduction, predicates.size(),
					mOverallPositionsWithReduction, mOverallTrivial, mOverallUnknowns));
			return new TracePredicates(input.getPrecondition(), input.getPostcondition(), predicates);
		}

		private void setRefinedPredicate(final List<IPredicate> predicates,
				final List<IPredicatePostprocessor> postprocs, final IPredicate predecessor, final int pos,
				final PredicateReductionResult res) {
			if (res.sizeReduction() > 0) {
				predicates.set(pos, res.result());
				mOverallSizeReduction += res.sizeReduction();
				mOverallPositionsWithReduction++;
			} else {
				predicates.set(pos, applyPostprocessors(postprocs, pos, predecessor));
			}
			mOverallUnknowns += res.solverReturnedUnknown();
		}

		private PredicateReductionResult constructReduction(final List<IPredicatePostprocessor> postprocs,
				final List<IPredicate> predecessorConjuncts, final int pos, final PrecondRelevanceResult checkResult) {
			switch (checkResult.validity()) {
			case INVALID:
				throw new AssertionError("Unexpected invalidity of Hoare triple for position " + pos);
			case UNKNOWN:
				// Cannot simplify because we did not get an unsat core.
				mLogger.warn("Hoare triple for position " + pos + " is unknown");
				return new PredicateReductionResult(null, (byte) 1, 0);
			case VALID:
				final List<IPredicate> relevantPreconditions = checkResult.relevantPreconditions();
				final int sizeReduction = predecessorConjuncts.size() - relevantPreconditions.size();
				if (sizeReduction == 0) {
					return new PredicateReductionResult(null, (byte) 0, 0);
				}
				assert sizeReduction > 0 : "Size reduction must be positive";
				mLogger.warn(String.format("Reduced conjuncts from %s to %s for position %s",
						predecessorConjuncts.size(), relevantPreconditions.size(), pos));
				final HashSet<IPredicate> irrelevantConjuncts = new HashSet<>(predecessorConjuncts);
				irrelevantConjuncts.removeAll(relevantPreconditions);
				mLogger.warn(String.format("Irrelevant conjuncts for position %s: %s", pos, irrelevantConjuncts));

				// No need to simplify, the conjunction is a subset of an existing conjunction.
				IPredicate refined = mPredicateFactory.and(SimplificationTechnique.NONE, relevantPreconditions);
				refined = applyPostprocessors(postprocs, pos, refined);
				return new PredicateReductionResult(refined, (byte) 0, sizeReduction);
			default:
				throw new AssertionError("Unexpected value" + checkResult.validity());
			}
		}

		private List<IPredicate> splitConjunctively(final IPredicate predicate) {
			final Term[] conjuncts = SmtUtils.getConjuncts(predicate.getFormula());
			final List<IPredicate> result = new ArrayList<>(conjuncts.length);
			for (final Term conjunct : conjuncts) {
				result.add(mPredicateFactory.newPredicate(conjunct));
			}
			return result;
		}

		record PredicateReductionResult(IPredicate result, byte solverReturnedUnknown, int sizeReduction) {
		}
	}

}
