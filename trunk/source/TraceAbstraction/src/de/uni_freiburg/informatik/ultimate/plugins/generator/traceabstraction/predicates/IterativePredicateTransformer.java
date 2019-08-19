/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgReturnTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.linearterms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.TraceInterpolationException.Reason;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.NestedFormulas;

/**
 * Compute sequence of predicates via strongest post or weakest precondition along a trace.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class IterativePredicateTransformer {

	private enum BackwardSequence {
		PRE, WP
	};

	private final ModifiableGlobalsTable mModifiedGlobals;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final ManagedScript mMgdScript;

	private final PredicateTransformer<Term, IPredicate, TransFormula> mPredicateTransformer;
	private final PredicateFactory mPredicateFactory;
	private final NestedWord<? extends IAction> mTrace;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	protected final SortedMap<Integer, IPredicate> mPendingContexts;

	private final IPredicate mTruePredicate;

	private final IIcfgSymbolTable mSymbolTable;

	private static final boolean INTERPROCEDURAL_POST = true;
	private static final boolean TRANSFORM_SUMMARY_TO_CNF = true;

	/**
	 * 
	 * @param truePredicate
	 *            only required if you want to compute the non-inductive wp sequence in which the call predecessor is
	 *            always the true predicate
	 */
	public IterativePredicateTransformer(final PredicateFactory predicateFactory, final ManagedScript mgdScript,
			final ModifiableGlobalsTable modifiableGlobalsTable, final IUltimateServiceProvider services,
			final NestedWord<? extends IAction> trace, final IPredicate precondition, final IPredicate postcondition,
			final SortedMap<Integer, IPredicate> pendingContexts, final IPredicate truePredicate,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
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
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> nf,
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
			return new TracePredicates(mPrecondition, computedPostcondition, Arrays.asList(spSequence));
		}
		return ipp;
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
		private final ILogger mLogger;
		private final ManagedScript mMgdScript;
		private final PredicateFactory mPredicateFactory;
		private final SimplificationTechnique mSimplificationTechnique;
		private final XnfConversionTechnique mXnfConversionTechnique;

		public QuantifierEliminationPostprocessor(final IUltimateServiceProvider services, final ILogger logger,
				final ManagedScript boogie2smt, final PredicateFactory predicateFactory,
				final SimplificationTechnique simplificationTechnique,
				final XnfConversionTechnique xnfConversionTechnique) {
			super();
			mServices = services;
			mLogger = logger;
			mMgdScript = boogie2smt;
			mPredicateFactory = predicateFactory;
			mSimplificationTechnique = simplificationTechnique;
			mXnfConversionTechnique = xnfConversionTechnique;
		}

		@Override
		public IPredicate postprocess(final IPredicate pred, final int i) {
			final Term lessQuantifier = PartialQuantifierElimination.tryToEliminate(mServices, mLogger, mMgdScript,
					pred.getFormula(), mSimplificationTechnique, mXnfConversionTechnique);
			// 2016-05-14 Matthias: Which structure of the resulting
			// formula is better? 1. Prenex normal form (quantifiers outside)
			// or 2. a form where quantifiers are pushed inside.
			// Option 2. allows us to simplify the formula with SimplifyDDA
			// (which considers quantified formulas as atoms).
			// However, SimplifyDDA may waste a lot of time.
			// A small evaluation that I did today (using Z3) shows that
			// there is not much difference between both variants.
			final Term resultTerm = new QuantifierPusher(mMgdScript, mServices, false, PqeTechniques.ONLY_DER)
					.transform(lessQuantifier);
			// resultTerm = new PrenexNormalForm(mMgdScript).transform(lessQuantifier);
			final IPredicate result = mPredicateFactory.newPredicate(resultTerm);
			return result;
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
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> nf,
			final List<IPredicatePostprocessor> postprocs, final boolean useTrueAsCallPredecessor,
			final boolean alternatingQuantifierBailout) throws TraceInterpolationException {
		return computeBackwardSequence(nf, postprocs, useTrueAsCallPredecessor, alternatingQuantifierBailout,
				BackwardSequence.WP);
	}

	public TracePredicates computePreSequence(final NestedFormulas<UnmodifiableTransFormula, IPredicate> nf,
			final List<IPredicatePostprocessor> postprocs, final boolean alternatingQuantifierBailout)
			throws TraceInterpolationException {
		return computeBackwardSequence(nf, postprocs, true, alternatingQuantifierBailout, BackwardSequence.PRE);
	}

	public TracePredicates computeBackwardSequence(final NestedFormulas<UnmodifiableTransFormula, IPredicate> nf,
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
				final UnmodifiableTransFormula returnTf = nf.getFormulaFromNonCallPos(i);

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
					callLocalVarsAssignment = nf.getLocalVarAssignment(callPos);
					oldVarAssignments = nf.getOldVarAssignment(callPos);
					final UnmodifiableTransFormula globalVarsAssignments = nf.getGlobalVarAssignment(callPos);
					final ProcedureSummary summary = computeProcedureSummary(mTrace, callLocalVarsAssignment, returnTf,
							oldVarAssignments, globalVarsAssignments, nf, callPos, i);

					final Term preOrWpOfSummaryTerm;
					if (bs == BackwardSequence.WP) {
						preOrWpOfSummaryTerm =
								mPredicateTransformer.weakestPrecondition(successorWp, summary.getWithCallAndReturn());
					} else {
						preOrWpOfSummaryTerm = SmtUtils.not(mMgdScript.getScript(),
								mPredicateTransformer.weakestPrecondition(successorWp, summary.getWithCallAndReturn()));
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
				}
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

	private static final class ProcedureSummary {
		private final UnmodifiableTransFormula mWithCallAndReturn;
		private final UnmodifiableTransFormula mWithoutCallAndReturn;

		public ProcedureSummary(final UnmodifiableTransFormula withCallAndReturn,
				final UnmodifiableTransFormula withoutCallAndReturn) {
			super();
			mWithCallAndReturn = withCallAndReturn;
			mWithoutCallAndReturn = withoutCallAndReturn;
		}

		public UnmodifiableTransFormula getWithCallAndReturn() {
			return mWithCallAndReturn;
		}

		public UnmodifiableTransFormula getWithoutCallAndReturn() {
			return mWithoutCallAndReturn;
		}

	}

	/**
	 * Computes a summary of the procedure. The procedure consists (or is represented) by the Call statement, the Return
	 * statement and the inner statements.
	 * 
	 * @param trace
	 *            - the inner statements of the procedure
	 * @param callTf
	 * @param returnTf
	 * @param oldVarsAssignmentTf
	 * @param rv
	 * @param callPos
	 * @return
	 */
	private ProcedureSummary computeProcedureSummary(final NestedWord<? extends IAction> trace,
			final UnmodifiableTransFormula callTf, final UnmodifiableTransFormula returnTf,
			final UnmodifiableTransFormula oldVarsAssignmentTf, final UnmodifiableTransFormula globalVarsAssignment,
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> rv, final int callPos, final int returnPos) {
		final UnmodifiableTransFormula summaryOfInnerStatements =
				computeSummaryForInterproceduralTrace(trace, rv, callPos + 1, returnPos);
		final String callee = ((ICallAction) trace.getSymbol(callPos)).getSucceedingProcedure();
		final UnmodifiableTransFormula summaryWithCallAndReturn =
				TransFormulaUtils.sequentialCompositionWithCallAndReturn(mMgdScript, true, false,
						TRANSFORM_SUMMARY_TO_CNF, callTf, oldVarsAssignmentTf, globalVarsAssignment,
						summaryOfInnerStatements, returnTf, mLogger, mServices, mXnfConversionTechnique,
						mSimplificationTechnique, mSymbolTable, mModifiedGlobals.getModifiedBoogieVars(callee));
		return new ProcedureSummary(summaryWithCallAndReturn, summaryOfInnerStatements);
	}

	/**
	 * Computes a summary for the given trace, but only for the statements from position "start" to position "end".
	 * 
	 * @return - a summary for the statements from the given trace from position "start" to position "end"
	 */
	private UnmodifiableTransFormula computeSummaryForInterproceduralTrace(final NestedWord<? extends IAction> trace,
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> rv, final int start, final int end) {
		final LinkedList<UnmodifiableTransFormula> transformulasToComputeSummaryFor = new LinkedList<>();
		for (int i = start; i < end; i++) {
			if (trace.getSymbol(i) instanceof ICallAction) {
				final UnmodifiableTransFormula callTf = rv.getLocalVarAssignment(i);
				final UnmodifiableTransFormula oldVarsAssignment = rv.getOldVarAssignment(i);
				final UnmodifiableTransFormula globalVarsAssignment = rv.getGlobalVarAssignment(i);
				if (!trace.isPendingCall(i)) {
					// Case: non-pending call
					// Compute a summary for Call and corresponding Return, but
					// only if the position of the corresponding
					// Return is smaller than the position "end"
					final int returnPosition = trace.getReturnPosition(i);
					if (returnPosition < end) {
						// 1. Compute a summary for the statements between this
						// non-pending Call
						// and the corresponding Return recursively
						final UnmodifiableTransFormula summaryBetweenCallAndReturn =
								computeSummaryForInterproceduralTrace(trace, rv, i + 1, returnPosition);
						final UnmodifiableTransFormula returnTf = rv.getFormulaFromNonCallPos(returnPosition);
						final String callee = ((ICallAction) trace.getSymbol(i)).getSucceedingProcedure();
						transformulasToComputeSummaryFor
								.addLast(TransFormulaUtils.sequentialCompositionWithCallAndReturn(mMgdScript, true,
										false, TRANSFORM_SUMMARY_TO_CNF, callTf, oldVarsAssignment,
										globalVarsAssignment, summaryBetweenCallAndReturn, returnTf, mLogger, mServices,
										mXnfConversionTechnique, mSimplificationTechnique, mSymbolTable,
										mModifiedGlobals.getModifiedBoogieVars(callee)));
						i = returnPosition;
					} else {
						// If the position of the corresponding Return is >=
						// "end",
						// then we handle this case as a pending-call
						final UnmodifiableTransFormula summaryAfterPendingCall =
								computeSummaryForInterproceduralTrace(trace, rv, i + 1, end);
						final String nameEndProcedure = trace.getSymbol(end).getSucceedingProcedure();
						final Set<IProgramNonOldVar> modifiableGlobalsOfEndProcedure =
								mModifiedGlobals.getModifiedBoogieVars(nameEndProcedure);
						return TransFormulaUtils.sequentialCompositionWithPendingCall(mMgdScript, true, false,
								TRANSFORM_SUMMARY_TO_CNF, transformulasToComputeSummaryFor, callTf, oldVarsAssignment,
								globalVarsAssignment, summaryAfterPendingCall, mLogger, mServices,
								modifiableGlobalsOfEndProcedure, mXnfConversionTechnique, mSimplificationTechnique,
								mSymbolTable, trace.getSymbol(start).getPrecedingProcedure(),
								trace.getSymbol(i).getPrecedingProcedure(), trace.getSymbol(i).getSucceedingProcedure(),
								nameEndProcedure, mModifiedGlobals);
					}
				} else {
					final UnmodifiableTransFormula summaryAfterPendingCall =
							computeSummaryForInterproceduralTrace(trace, rv, i + 1, end);
					final String nameEndProcedure = trace.getSymbol(end).getSucceedingProcedure();
					final Set<IProgramNonOldVar> modifiableGlobalsOfEndProcedure =
							mModifiedGlobals.getModifiedBoogieVars(nameEndProcedure);
					return TransFormulaUtils.sequentialCompositionWithPendingCall(mMgdScript, true, false,
							TRANSFORM_SUMMARY_TO_CNF, transformulasToComputeSummaryFor, callTf, oldVarsAssignment, null,
							summaryAfterPendingCall, mLogger, mServices, modifiableGlobalsOfEndProcedure,
							mXnfConversionTechnique, mSimplificationTechnique, mSymbolTable,
							trace.getSymbol(start).getPrecedingProcedure(), trace.getSymbol(i).getPrecedingProcedure(),
							trace.getSymbol(i).getSucceedingProcedure(), nameEndProcedure, mModifiedGlobals);
				}
			} else if (trace.getSymbol(i) instanceof IReturnAction) {
				// Nothing to do
			} else {
				transformulasToComputeSummaryFor.addLast(rv.getFormulaFromNonCallPos(i));
			}
		}
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, true, false,
				TRANSFORM_SUMMARY_TO_CNF, mXnfConversionTechnique, mSimplificationTechnique,
				transformulasToComputeSummaryFor);
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
			super();
			mReason = reason;
		}

		public Reason getReason() {
			return mReason;
		}

	}

}
