/*
 * Copyright (C) 2026 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2026 University of Freiburg
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
import java.util.Collection;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerWithPreconditionRelevanceAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerWithPreconditionRelevanceAnalysis.PrecondRelevanceResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.TracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class HoareCoreBackwardPostprocessor<L extends IAction> {

	private final CfgSmtToolkit mCsToolkit;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	private final ILogger mLogger;
	private final NestedWord<L> mTrace;
	private final SortedMap<Integer, IPredicate> mPendingContexts;
	private final BasicPredicateFactory mPredicateFactory;
	private final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> mRtf;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final SimplificationTechnique mSimplificationTechnique;
	private final IIcfgSymbolTable mSymbolTable;
	private final ModifiableGlobalsTable mModifiedGlobals;
	private final Map<Integer, List<IPredicate>> mPredConjunctsOfNonPendingCallRelevantFromReturn = new HashMap<>();
	private final Map<Integer, List<IPredicate>> mPredConjunctsOfNonPendingCall = new HashMap<>();

	private int mOverallSizeReduction;
	private int mOverallUnknowns;
	private int mOverallConjuncts;
	private int mOverallPositionsWithReduction;
	private int mOverallTrivial;

	private HoareCoreBackwardPostprocessor(final CfgSmtToolkit csToolkit, final IPredicate precondition,
			final IPredicate postcondition, final ILogger logger, final NestedWord<L> trace,
			final SortedMap<Integer, IPredicate> pendingContexts, final BasicPredicateFactory predicateFactory,
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rtf, final ManagedScript mgdScript,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final IIcfgSymbolTable symbolTable, final ModifiableGlobalsTable modifiedGlobals) {
		mCsToolkit = csToolkit;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mLogger = logger;
		mTrace = trace;
		mPendingContexts = pendingContexts;
		mPredicateFactory = predicateFactory;
		mRtf = rtf;
		mMgdScript = mgdScript;
		mServices = services;
		mSimplificationTechnique = simplificationTechnique;
		mSymbolTable = symbolTable;
		mModifiedGlobals = modifiedGlobals;
	}

	public static <L extends IAction> TracePredicates apply(final CfgSmtToolkit csToolkit,
			final IPredicate precondition, final IPredicate postcondition, final ILogger logger,
			final NestedWord<L> trace, final SortedMap<Integer, IPredicate> pendingContexts,
			final BasicPredicateFactory predicateFactory,
			final NestedFormulas<L, UnmodifiableTransFormula, IPredicate> rtf, final ManagedScript mgdScript,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique,
			final IIcfgSymbolTable symbolTable, final ModifiableGlobalsTable modifiedGlobals,
			final List<IPredicatePostprocessor> postprocs, final TracePredicates input) {
		final HoareCoreBackwardPostprocessor<L> postprocessor = new HoareCoreBackwardPostprocessor<>(csToolkit,
				precondition, postcondition, logger, trace, pendingContexts, predicateFactory, rtf, mgdScript, services,
				simplificationTechnique, symbolTable, modifiedGlobals);
		return postprocessor.doWork(input, postprocs);
	}

	TracePredicates doWork(final TracePredicates input, final List<IPredicatePostprocessor> postprocs) {
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
				final int pos = i;
				final IAction action = mTrace.getSymbol(pos);
				switch (action) {
				case final IInternalAction internalAction: {
					if (!mTrace.isInternalPosition(pos)) {
						throw new AssertionError("not an internal action at internal position");
					}
					final IInternalAction relevantInternalAction =
							constructRelevantInternalAction(internalAction, mRtf.getFormulaFromNonCallPos(i));

					final List<IPredicate> predecessorConjuncts = splitConjunctively(predecessor);
					mOverallConjuncts += predecessorConjuncts.size();

					final IPredicate result = handleInternalAction(checker, predecessor, successor,
							predecessorConjuncts, pos, relevantInternalAction);
					predicates.set(i, applyPostprocessors(postprocs, i, result));
					break;
				}
				case final ICallAction callAction: {
					if (!mTrace.isCallPosition(pos)) {
						throw new AssertionError("not a call action at call position");
					}
					final ICallAction relevantCallAction =
							constructRelevantCallAction(callAction, mRtf.getLocalVarAssignment(i));

					if (mTrace.isPendingCall(pos)) {
						final List<IPredicate> predecessorConjuncts = splitConjunctively(predecessor);
						mOverallConjuncts += predecessorConjuncts.size();
						final IPredicate result = handlePendingCallAction(checker, predecessor, successor,
								predecessorConjuncts, pos, relevantCallAction);
						predicates.set(i, applyPostprocessors(postprocs, i, result));
					} else {
						final List<IPredicate> predecessorConjuncts = mPredConjunctsOfNonPendingCall.get(pos);
						final IPredicate result = handleNonPendingCallAction(checker, predecessor, successor,
								predecessorConjuncts, pos, relevantCallAction);
						predicates.set(i, applyPostprocessors(postprocs, i, result));

					}
					break;
				}
				case final IReturnAction returnAction: {
					if (!mTrace.isReturnPosition(pos)) {
						throw new AssertionError("not a return action at return position");
					}
					final List<IPredicate> predecessorConjuncts = splitConjunctively(predecessor);
					mOverallConjuncts += predecessorConjuncts.size();
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
							final UnmodifiableTransFormula summaryTf = TraceCheckUtils.computeProcedureSummary(mTrace,
									mRtf, callPos, pos, mMgdScript, mServices, mLogger, mSimplificationTechnique,
									mSymbolTable, mModifiedGlobals, false);
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
							mPredConjunctsOfNonPendingCall.put(callPos, hierPreConjuncts);
							final PrecondRelevanceResult checkResult =
									checker.checkInternal(hierPreConjuncts, summary, successor);
							final List<IPredicate> relevantPreconditions = handleRelevanceResult(pos, checkResult);
							if (relevantPreconditions != null) {
								mPredConjunctsOfNonPendingCallRelevantFromReturn.put(callPos, relevantPreconditions);
								// No need to simplify, the conjunction is a subset of an existing conjunction.
								hierPre = mPredicateFactory.and(SimplificationTechnique.NONE, relevantPreconditions);
							}
//							hierPre = applyPostprocessors(postprocs, callPos, hierPre);
//							predicates.set(callPos, hierPre);
						}
					}

					final IReturnAction relevantReturnAction = constructRelevantReturnAction(returnAction,
							mRtf.getFormulaFromNonCallPos(pos), mRtf.getLocalVarAssignment(callPos));

					final IPredicate result = handleReturnActionLinearPredecessor(checker, predecessor, hierPre,
							successor, predecessorConjuncts, pos, relevantReturnAction);
					predicates.set(i, applyPostprocessors(postprocs, i, result));
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
		return new TracePredicates(mPrecondition, mPostcondition, predicates);
	}

	private static IInternalAction constructRelevantInternalAction(final IInternalAction internalAction,
			final UnmodifiableTransFormula tf) {
		return new IInternalAction() {

			@Override
			public String getPrecedingProcedure() {
				return internalAction.getPrecedingProcedure();
			}

			@Override
			public String getSucceedingProcedure() {
				return internalAction.getSucceedingProcedure();
			}

			@Override
			public String toString() {
				return String.valueOf(tf);
			}

			@Override
			public UnmodifiableTransFormula getTransformula() {
				return tf;

			}
		};
	}

	private static ICallAction constructRelevantCallAction(final ICallAction callAction,
			final UnmodifiableTransFormula tf) {
		return new ICallAction() {

			@Override
			public String getPrecedingProcedure() {
				return callAction.getPrecedingProcedure();
			}

			@Override
			public String getSucceedingProcedure() {
				return callAction.getSucceedingProcedure();
			}

			@Override
			public String toString() {
				return String.valueOf(tf);
			}

			@Override
			public UnmodifiableTransFormula getTransformula() {
				return tf;

			}

			@Override
			public UnmodifiableTransFormula getLocalVarsAssignment() {
				return getTransformula();
			}
		};
	}

	private static IReturnAction constructRelevantReturnAction(final IReturnAction returnAction,
			final UnmodifiableTransFormula returnTf, final UnmodifiableTransFormula localVarsAssignmentOfCallTf) {
		return new IReturnAction() {

			@Override
			public String getPrecedingProcedure() {
				return returnAction.getPrecedingProcedure();
			}

			@Override
			public String getSucceedingProcedure() {
				return returnAction.getSucceedingProcedure();
			}

			@Override
			public String toString() {
				return String.valueOf(returnTf);
			}

			@Override
			public UnmodifiableTransFormula getTransformula() {
				return returnTf;

			}

			@Override
			public UnmodifiableTransFormula getAssignmentOfReturn() {
				return getTransformula();
			}

			@Override
			public UnmodifiableTransFormula getLocalVarsAssignmentOfCall() {
				return localVarsAssignmentOfCallTf;
			}
		};
	}

	private IPredicate handleInternalAction(final HoareTripleCheckerWithPreconditionRelevanceAnalysis checker,
			final IPredicate predecessor, final IPredicate successor, final List<IPredicate> predecessorConjuncts,
			final int pos, final IInternalAction internalAction) {
		if (SmtUtils.isTrueLiteral(predecessor.getFormula()) || SmtUtils.isFalseLiteral(predecessor.getFormula())) {
			mOverallTrivial++;
			return predecessor;
		}
		final PrecondRelevanceResult checkResult =
				checker.checkInternal(predecessorConjuncts, internalAction, successor);
		final List<IPredicate> relevantPreconditions = handleRelevanceResult(pos, checkResult);
		if (relevantPreconditions == null) {
			return predecessor;
		}
		return handleRelevantPreconditions(relevantPreconditions, predecessorConjuncts, predecessor, pos);
	}

	private IPredicate handlePendingCallAction(final HoareTripleCheckerWithPreconditionRelevanceAnalysis checker,
			final IPredicate predecessor, final IPredicate successor, final List<IPredicate> predecessorConjuncts,
			final int pos, final ICallAction callAction) {
		if (SmtUtils.isTrueLiteral(predecessor.getFormula()) || SmtUtils.isFalseLiteral(predecessor.getFormula())) {
			mOverallTrivial++;
			return predecessor;
		}
		final PrecondRelevanceResult checkResult = checker.checkCall(predecessorConjuncts, callAction, successor);
		final List<IPredicate> relevantPreconditions = handleRelevanceResult(pos, checkResult);
		if (relevantPreconditions == null) {
			return predecessor;
		}
		return handleRelevantPreconditions(relevantPreconditions, predecessorConjuncts, predecessor, pos);
	}

	private IPredicate handleNonPendingCallAction(final HoareTripleCheckerWithPreconditionRelevanceAnalysis checker,
			final IPredicate predecessor, final IPredicate successor, final List<IPredicate> predecessorConjuncts,
			final int pos, final ICallAction callAction) {
		final List<IPredicate> hierPredRelevantConjunctsFromReturn =
				mPredConjunctsOfNonPendingCallRelevantFromReturn.get(pos);
		if (hierPredRelevantConjunctsFromReturn == null) {
			// return already disallowed reduction.
			return predecessor;
		}
		if (!SmtUtils.isTrueLiteral(successor.getFormula())) {
//			throw new AssertionError("Successor not true literal, but " + successor.getFormula().toString());
			successor.getFormula().toString();
		}
		final PrecondRelevanceResult checkResult = checker.checkCall(predecessorConjuncts, callAction, successor);
		final List<IPredicate> relevantPreconditions = handleRelevanceResult(pos, checkResult);
		if (relevantPreconditions == null) {
			return predecessor;
		}
		final Set<IPredicate> union = new HashSet<>(hierPredRelevantConjunctsFromReturn);
		final boolean test = union.addAll(relevantPreconditions);
		if (test) {
			throw new AssertionError("Wow, the call has an influence.");
		}
		return handleRelevantPreconditions(union, predecessorConjuncts, predecessor, pos);
	}

	private IPredicate handleReturnActionLinearPredecessor(
			final HoareTripleCheckerWithPreconditionRelevanceAnalysis checker, final IPredicate linearPredecessor,
			final IPredicate hierarchicalPredecessor, final IPredicate successor,
			final List<IPredicate> predecessorConjuncts, final int pos, final IReturnAction returnAction) {
		if (SmtUtils.isTrueLiteral(linearPredecessor.getFormula())
				|| SmtUtils.isFalseLiteral(linearPredecessor.getFormula())) {
			mOverallTrivial++;
			return linearPredecessor;
		}
		final PrecondRelevanceResult checkResult =
				checker.checkReturn(predecessorConjuncts, hierarchicalPredecessor, returnAction, successor);
		final List<IPredicate> relevantPreconditions = handleRelevanceResult(pos, checkResult);
		if (relevantPreconditions == null) {
			return linearPredecessor;
		}
		return handleRelevantPreconditions(relevantPreconditions, predecessorConjuncts, linearPredecessor, pos);
	}

	private IPredicate handleRelevantPreconditions(final Collection<IPredicate> relevantPreconditions,
			final List<IPredicate> predecessorConjuncts, final IPredicate predecessor, final int pos) {
		final int sizeReduction = predecessorConjuncts.size() - relevantPreconditions.size();
		if (sizeReduction == 0) {
			return predecessor;
		}
		assert sizeReduction > 0 : "Size reduction must be positive";
		mOverallSizeReduction += sizeReduction;
		mOverallPositionsWithReduction++;
		mLogger.warn(String.format("Reduced conjuncts from %s to %s for position %s", predecessorConjuncts.size(),
				relevantPreconditions.size(), pos));
		final HashSet<IPredicate> irrelevantConjuncts = new HashSet<>(predecessorConjuncts);
		irrelevantConjuncts.removeAll(relevantPreconditions);
		mLogger.warn(String.format("Irrelevant conjuncts for position %s: %s", pos, irrelevantConjuncts));

		// No need to simplify, the conjunction is a subset of an existing conjunction.
		return mPredicateFactory.and(SimplificationTechnique.NONE, relevantPreconditions);
	}

	private List<IPredicate> handleRelevanceResult(final int pos, final PrecondRelevanceResult checkResult) {
		switch (checkResult.validity()) {
		case INVALID:
			throw new AssertionError("Unexpected invalidity of Hoare triple for position " + pos);
		case UNKNOWN:
			// Cannot simplify because we did not get an unsat core.
			mOverallUnknowns++;
			mLogger.warn("Hoare triple for position " + pos + " is unknown");
			return null;
		case VALID:
			return checkResult.relevantPreconditions();
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

	private static IPredicate applyPostprocessors(final List<IPredicatePostprocessor> postprocs, final int i,
			final IPredicate pred) {
		IPredicate postprocessed = pred;
		for (final IPredicatePostprocessor postproc : postprocs) {
			postprocessed = postproc.postprocess(postprocessed, i);
		}
		return postprocessed;
	}

	record PredicateReductionResult(IPredicate result, byte solverReturnedUnknown, int sizeReduction) {
	}
}
