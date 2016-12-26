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
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * Compute sequence of predicates via strongest post or weakest precondition
 * along a trace.
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class IterativePredicateTransformer {
	private final ModifiableGlobalsTable mModifiedGlobals;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;
	private final ManagedScript mMgdScript;
	
	private final PredicateTransformer mPredicateTransformer;
	private final PredicateFactory mPredicateFactory;
	private final NestedWord<? extends IAction> mTrace;
	private final IPredicate mPrecondition;
	private final IPredicate mPostcondition;
	protected final SortedMap<Integer, IPredicate> mPendingContexts;
	private final IPredicate mFalsePredicate;
	private final boolean mInterproceduralPost = true;
	private final IIcfgSymbolTable mSymbolTable;
	
	private static final boolean s_TransformSummaryToCNF = true;

	public IterativePredicateTransformer(final PredicateFactory predicateFactory,
			final ManagedScript mgdScript,
			final ModifiableGlobalsTable modifiableGlobalsTable,
			final IUltimateServiceProvider services,
			final NestedWord<? extends IAction> trace, final IPredicate precondition,
			final IPredicate postcondition, final SortedMap<Integer, IPredicate> pendingContexts,
			final IPredicate falsePredicate,
			final SimplificationTechnique simplificationTechnique,
			final XnfConversionTechnique xnfConversionTechnique, final IIcfgSymbolTable symbolTable) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mMgdScript = mgdScript;
		mModifiedGlobals = modifiableGlobalsTable;
		mPredicateTransformer = new PredicateTransformer(services,
				mgdScript, simplificationTechnique, xnfConversionTechnique);
		mPredicateFactory = predicateFactory;
		mTrace = trace;
		mPrecondition = precondition;
		mPostcondition = postcondition;
		mPendingContexts = pendingContexts;
		mFalsePredicate = falsePredicate;
		mSymbolTable = symbolTable;
	}
	

	
	public interface PredicatePostprocessor {
		/**
		 * Do post processing for the predicate before the i'th action of
		 * the trace. This means especially, that if i==0 we do the post
		 * processing for the precondition and if i==trace.length() we do
		 * the post processing for the postcondition.
		 */
		IPredicate postprocess(IPredicate pred, int i);
	}
	
	
	
	/**
	 * Compute sequence of strongest postcondition along a trace.
	 * Start with the given precondition and compute iteratively
	 * {@link IPredicate}s using the SP predicate transformer.
	 * @param nf representation of the trace along which we compute the SP
	 * 	sequence
	 * @param postprocs List of postprocessors that apply to each IPredicate
	 * after it was constructed via SP. May be empty.
	 * 	TODO: If the given postcondition is null, we also compute a precondition
	 * (IPredicate before the first {@link IAction} in the trace)
	 */
	public InterpolantsPreconditionPostcondition computeStrongestPostconditionSequence(
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> nf, final List<PredicatePostprocessor> postprocs) {
		final IPredicate[] spSequence = new IPredicate[mTrace.length() - 1];
		final InterpolantsPreconditionPostcondition ipp = new InterpolantsPreconditionPostcondition(
				mPrecondition, mPostcondition, Arrays.asList(spSequence));

		for (int i = 0; i < mTrace.length() - 1; i++) {
			final IPredicate predecessor = ipp.getInterpolant(i);
			final Term spTerm;
			if (mTrace.getSymbol(i) instanceof Call) {
				final Call call = (Call) mTrace.getSymbol(i);
				final String calledMethod = call.getCallStatement().getMethodName();
				final Set<IProgramNonOldVar> modifiedGlobals = mModifiedGlobals.getModifiedBoogieVars(calledMethod);
				if (mTrace.isPendingCall(i) || !mInterproceduralPost ) {
					spTerm = mPredicateTransformer.strongestPostconditionCall(
							predecessor, nf.getLocalVarAssignment(i),
							nf.getGlobalVarAssignment(i), nf.getOldVarAssignment(i),
							modifiedGlobals);
				} else {
					spTerm = mPredicateTransformer.weakLocalPostconditionCall(
							predecessor,
							nf.getGlobalVarAssignment(i),
							modifiedGlobals);
				}
			} else if (mTrace.getSymbol(i) instanceof Return) {
				final IPredicate callerPred;
				final UnmodifiableTransFormula callGlobalVarsAssignment;
				final UnmodifiableTransFormula callOldVarsAssignment;
				final UnmodifiableTransFormula callLocalVarsAssignment;
				if (mTrace.isPendingReturn(i)) {
					callerPred = mPendingContexts.get(i);
					callOldVarsAssignment = nf.getOldVarAssignment(i);
					callGlobalVarsAssignment = null;
					callLocalVarsAssignment = nf.getLocalVarAssignment(i);
				} else {
					final int callPos = mTrace.getCallPosition(i);
					assert callPos >= 0 && callPos <= i : "Bad call position!";
					callerPred = ipp.getInterpolant(callPos);
					callGlobalVarsAssignment = nf.getGlobalVarAssignment(callPos);
					callOldVarsAssignment = null;
					callLocalVarsAssignment = nf.getLocalVarAssignment(callPos);
				}
				final UnmodifiableTransFormula returnTransFormula = nf.getFormulaFromNonCallPos(i);
				spTerm = mPredicateTransformer.strongestPostcondition(
						predecessor, callerPred,
						returnTransFormula, callLocalVarsAssignment,
						callGlobalVarsAssignment, callOldVarsAssignment);
			} else {
				spTerm = mPredicateTransformer.strongestPostcondition(
						predecessor,
						nf.getFormulaFromNonCallPos(i));
			}
			final IPredicate sp = constructPredicate(spTerm);
			spSequence[i] = applyPostprocessors(postprocs, i+1, sp);
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
	
	
	public static class QuantifierEliminationPostprocessor implements PredicatePostprocessor {
		
		private final IUltimateServiceProvider mServices;
		private final ILogger mLogger;
		private final ManagedScript mMgdScript;
		private final PredicateFactory mPredicateFactory;
		private final SimplificationTechnique mSimplificationTechnique;
		private final XnfConversionTechnique mXnfConversionTechnique;
		

		public QuantifierEliminationPostprocessor(
				final IUltimateServiceProvider services,
				final ILogger logger, final ManagedScript boogie2smt,
				final PredicateFactory predicateFactory,
				final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
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
			final Term lessQuantifier = PartialQuantifierElimination.tryToEliminate(
					mServices, mLogger, mMgdScript,
					pred.getFormula(), mSimplificationTechnique, mXnfConversionTechnique);
			final Term resultTerm;
			{
				// 2016-05-14 Matthias: Which structure of the resulting
				// formula is better? 1. Prenex normal form (quantifiers outside)
				// or 2. a form where quantifiers are pushed inside.
				// Option 2. allows us to simplify the formula with SimplifyDDA
				// (which considers quantified formulas as atoms).
				// However, SimplifyDDA may waste a lot of time.
				// A small evaluation that I did today (using Z3) shows that
				// there is not much difference between both variants.
				resultTerm = new QuantifierPusher(mMgdScript,
						mServices).transform(lessQuantifier);
//				resultTerm = new PrenexNormalForm(mBoogie2SMT.getScript(),
//									mBoogie2SMT.getVariableManager()).transform(lessQuantifier);
			}
			final IPredicate result = mPredicateFactory.newPredicate(resultTerm);
			return result;
		}
	}

	
	/**
	 * Compute sequence of weakest precondition along a trace.
	 * Start with the given postcondition and compute iteratively
	 * {@link IPredicate}s using the WP predicate transformer.
	 * If the given precondition is null, we also compute a precondition
	 * (IPredicate before the first {@link IAction} in the trace)
	 * @param nf representation of the trace along which we compute the WP
	 * 	sequence
	 * @param postprocs List of postprocessors that apply to each IPredicate
	 * after it was constructed via WP. May be empty.
	 */
	public InterpolantsPreconditionPostcondition computeWeakestPreconditionSequence(
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> nf, final List<PredicatePostprocessor> postprocs,
			final boolean callPredecessorIsAlwaysFalse) {
		final IPredicate[] wpSequence = new IPredicate[mTrace.length()-1];
		final InterpolantsPreconditionPostcondition ipp = new InterpolantsPreconditionPostcondition(
				mPrecondition, mPostcondition, Arrays.asList(wpSequence));
		/**
		 * Contains the predicates, which are computed during a Return with
		 * the second method, where the callerPred
		 * is computed as wp(returnerPred, summaryOfCalledProcedure).
		 */
		final Map<Integer, IPredicate> callerPredicatesComputed = new HashMap<Integer, IPredicate>();
		
		final boolean computePrecondition = (mPrecondition == null);
		final int positionOfFirstPredicate = (computePrecondition ? 0 : 1);
		IPredicate computedPrecondition = null;
		
		for (int i = mTrace.length()-1; i >= positionOfFirstPredicate; i--) {
			final Term wpTerm;
			
			final IPredicate successor = ipp.getInterpolant(i+1);
			if (mTrace.getSymbol(i) instanceof Call) {
				if (mTrace.isPendingCall(i)) {
					final Call call = (Call) mTrace.getSymbol(i);
					final String calledMethod = call.getCallStatement().getMethodName();
					final Set<IProgramNonOldVar> modifiedGlobals = mModifiedGlobals.getModifiedBoogieVars(calledMethod);
					wpTerm = mPredicateTransformer.weakestPrecondition(
							successor,
							nf.getLocalVarAssignment(i), nf.getGlobalVarAssignment(i),
							nf.getOldVarAssignment(i), modifiedGlobals);
				} else {
					// Call predecessor of non-pending calls are computed at
					// while processing the return
					assert callerPredicatesComputed.get(i) != null : "must have already been computed";
					wpTerm = null;
				}
			} else if (mTrace.getSymbol(i) instanceof Return) {
				final IPredicate callerPred;
				final UnmodifiableTransFormula globalVarsAssignments;
				final UnmodifiableTransFormula oldVarAssignments;
				final UnmodifiableTransFormula callLocalVarsAssignment;
				final UnmodifiableTransFormula returnTf = nf.getFormulaFromNonCallPos(i);
				final Return returnCB = (Return) mTrace.getSymbol(i);
				final String calledMethod = returnCB.getCallStatement().getMethodName();
				final Set<IProgramNonOldVar> modifiableGlobals = mModifiedGlobals.getModifiedBoogieVars(calledMethod);

				final Set<IProgramVar> varsOccurringBetweenCallAndReturn;
				if (mTrace.isPendingReturn(i)) {
					if (callPredecessorIsAlwaysFalse) {
						callerPred = mFalsePredicate;
					} else {
						callerPred = mPendingContexts.get(Integer.valueOf(i));
					}
					// we may get the local variable assignment (pending
					// context)
					// by requesting it at the position of the
					// pending-return.
					callLocalVarsAssignment = nf.getLocalVarAssignment(i);
					oldVarAssignments = nf.getOldVarAssignment(i);
					globalVarsAssignments = nf.getGlobalVarAssignment(i);
					// this is probably not yet supported
					varsOccurringBetweenCallAndReturn = null;
				} else {
					final int callPos = mTrace.getCallPosition(i);
					assert callPos >= 0 && callPos <= i : "Bad call position!";
					callLocalVarsAssignment = nf.getLocalVarAssignment(callPos);
					globalVarsAssignments = nf.getGlobalVarAssignment(callPos);
					oldVarAssignments = nf.getOldVarAssignment(callPos);
					final ProcedureSummary summary = computeProcedureSummary(
							mTrace, callLocalVarsAssignment, returnTf,
							oldVarAssignments, globalVarsAssignments, nf, callPos, i);
					varsOccurringBetweenCallAndReturn = summary.computeVariableInInnerSummary();
					final IPredicate wpOfSummary;
					{
						final Term wpOfSummary_Term = mPredicateTransformer.weakestPrecondition(
							successor, summary.getWithCallAndReturn());
						final IPredicate wpOfSummary_Predicate = constructPredicate(wpOfSummary_Term);
						wpOfSummary =
							applyPostprocessors(postprocs, callPos, wpOfSummary_Predicate);
					}
					callerPredicatesComputed.put(callPos, wpOfSummary);
					if (callPredecessorIsAlwaysFalse) {
						callerPred = mFalsePredicate;
					} else {
						callerPred = wpOfSummary;
					}
				}
				wpTerm = mPredicateTransformer.weakestPreconditionReturn(
						successor, callerPred, returnTf, callLocalVarsAssignment,
						globalVarsAssignments, oldVarAssignments, modifiableGlobals);
			} else {
				wpTerm = mPredicateTransformer.weakestPrecondition(
						successor, nf.getFormulaFromNonCallPos(i));
			}
			final IPredicate postprocessed;
			if ((mTrace.getSymbol(i) instanceof Call) && !mTrace.isPendingCall(i)) {
				// predicate was already constructed while processing the
				// corresponding return
				postprocessed = callerPredicatesComputed.get(i);
			} else {
				final IPredicate wp = constructPredicate(wpTerm);
				postprocessed = applyPostprocessors(postprocs, i, wp);
			}
			if (i == 0) {
				computedPrecondition = postprocessed;
			} else {
				wpSequence[i-1] = postprocessed;
			}
		}
		if (computePrecondition) {
			return new InterpolantsPreconditionPostcondition(
					computedPrecondition, mPostcondition, Arrays.asList(wpSequence));
		} else {
			return ipp;
		}
	}


	private IPredicate applyPostprocessors(
			final List<PredicatePostprocessor> postprocs, final int i, final IPredicate pred) {
		IPredicate postprocessed = pred;
		for (final PredicatePostprocessor postproc : postprocs) {
			postprocessed = postproc.postprocess(postprocessed, i);
		}
		return postprocessed;
	}
	
	
	private class ProcedureSummary {
		private final UnmodifiableTransFormula mWithCallAndReturn;
		private final UnmodifiableTransFormula mWithoutCallAndReturn;

		public ProcedureSummary(final UnmodifiableTransFormula withCallAndReturn, final UnmodifiableTransFormula withoutCallAndReturn) {
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

		/**
		 * Returns a set that contains all variables that occur in the summary
		 * without call and return.
		 */
		public Set<IProgramVar> computeVariableInInnerSummary() {
			return new Set<IProgramVar>() {

				@Override
				public boolean add(final IProgramVar e) {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean addAll(final Collection<? extends IProgramVar> c) {
					throw new UnsupportedOperationException();
				}

				@Override
				public void clear() {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean contains(final Object o) {
					return mWithoutCallAndReturn.getInVars().containsKey(o)
							|| mWithoutCallAndReturn.getOutVars().containsKey(o);
				}

				@Override
				public boolean containsAll(final Collection<?> c) {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean isEmpty() {
					throw new UnsupportedOperationException();
				}

				@Override
				public Iterator<IProgramVar> iterator() {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean remove(final Object o) {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean removeAll(final Collection<?> c) {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean retainAll(final Collection<?> c) {
					throw new UnsupportedOperationException();
				}

				@Override
				public int size() {
					throw new UnsupportedOperationException();
				}

				@Override
				public Object[] toArray() {
					throw new UnsupportedOperationException();
				}

				@Override
				public <T> T[] toArray(final T[] a) {
					throw new UnsupportedOperationException();
				}
			};
		}

	}
	
	
	/**
	 * Computes a summary of the procedure. The procedure consists (or is
	 * represented) by the Call statement, the Return statement and the inner
	 * statements.
	 * 
	 * @param trace
	 *            - the inner statements of the procedure
	 * @param Call
	 * @param Return
	 * @param oldVarsAssignment
	 * @param rv
	 * @param call_pos
	 * @return
	 */
	private ProcedureSummary computeProcedureSummary(final NestedWord<? extends IAction> trace, final UnmodifiableTransFormula Call,
			final UnmodifiableTransFormula Return, final UnmodifiableTransFormula oldVarsAssignment, final UnmodifiableTransFormula globalVarsAssignment,
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> rv,
			final int call_pos, final int return_pos) {
		final UnmodifiableTransFormula summaryOfInnerStatements = computeSummaryForInterproceduralTrace(
				trace, rv, call_pos + 1, return_pos);
		final String callee = ((ICallAction) trace.getSymbol(call_pos)).getSucceedingProcedure();
		final UnmodifiableTransFormula summaryWithCallAndReturn = TransFormulaUtils.sequentialCompositionWithCallAndReturn(
				mMgdScript, true, false, s_TransformSummaryToCNF, Call,
				oldVarsAssignment, globalVarsAssignment,
				summaryOfInnerStatements, Return, mLogger, mServices, mXnfConversionTechnique, mSimplificationTechnique,
				mSymbolTable, mModifiedGlobals.getModifiedBoogieVars(callee));
		return new ProcedureSummary(summaryWithCallAndReturn, summaryOfInnerStatements);
	}

	/**
	 * Computes a summary for the given trace, but only for the statements from
	 * position "start" to position "end".
	 * 
	 * @return - a summary for the statements from the given trace from position
	 *         "start" to position "end"
	 */
	private UnmodifiableTransFormula computeSummaryForInterproceduralTrace(final NestedWord<? extends IAction> trace,
			final NestedFormulas<UnmodifiableTransFormula, IPredicate> rv, final int start, final int end) {
		final LinkedList<UnmodifiableTransFormula> transformulasToComputeSummaryFor = new LinkedList<UnmodifiableTransFormula>();
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
						final UnmodifiableTransFormula summaryBetweenCallAndReturn = computeSummaryForInterproceduralTrace(trace, rv,
								i + 1, returnPosition);
						final UnmodifiableTransFormula returnTf = rv.getFormulaFromNonCallPos(returnPosition);
						final String callee = ((ICallAction) trace.getSymbol(i)).getSucceedingProcedure();
						transformulasToComputeSummaryFor.addLast(TransFormulaUtils.sequentialCompositionWithCallAndReturn(
								mMgdScript, true, false, s_TransformSummaryToCNF, callTf, oldVarsAssignment,
								globalVarsAssignment, summaryBetweenCallAndReturn, returnTf,
								mLogger, mServices, mXnfConversionTechnique, mSimplificationTechnique,
								mSymbolTable, mModifiedGlobals.getModifiedBoogieVars(callee)));
						i = returnPosition;
					} else {
						// If the position of the corresponding Return is >=
						// "end",
						// then we handle this case as a pending-call
						final UnmodifiableTransFormula summaryAfterPendingCall = computeSummaryForInterproceduralTrace(trace, rv, i + 1, end);
						final String nameEndProcedure = trace.getSymbol(end).getSucceedingProcedure();
						final Set<IProgramNonOldVar> modifiableGlobalsOfEndProcedure = mModifiedGlobals.getModifiedBoogieVars(nameEndProcedure);
						return TransFormulaUtils.sequentialCompositionWithPendingCall(mMgdScript, true,
								false, s_TransformSummaryToCNF, transformulasToComputeSummaryFor,
								callTf, oldVarsAssignment, globalVarsAssignment,
								summaryAfterPendingCall, mLogger, mServices, modifiableGlobalsOfEndProcedure,
								mXnfConversionTechnique, mSimplificationTechnique, mSymbolTable,
								trace.getSymbol(start).getPrecedingProcedure(), trace.getSymbol(i).getPrecedingProcedure(),
								trace.getSymbol(i).getSucceedingProcedure(), nameEndProcedure, mModifiedGlobals);
					}
				} else {
					final UnmodifiableTransFormula summaryAfterPendingCall = computeSummaryForInterproceduralTrace(trace, rv, i + 1, end);
					final String nameEndProcedure = trace.getSymbol(end).getSucceedingProcedure();
					final Set<IProgramNonOldVar> modifiableGlobalsOfEndProcedure = mModifiedGlobals.getModifiedBoogieVars(nameEndProcedure);
					return TransFormulaUtils.sequentialCompositionWithPendingCall(mMgdScript, true, false,
							s_TransformSummaryToCNF, transformulasToComputeSummaryFor,
							callTf, oldVarsAssignment, null, summaryAfterPendingCall,
							mLogger, mServices, modifiableGlobalsOfEndProcedure, mXnfConversionTechnique,
							mSimplificationTechnique, mSymbolTable,
							trace.getSymbol(start).getPrecedingProcedure(), trace.getSymbol(i).getPrecedingProcedure(),
							trace.getSymbol(i).getSucceedingProcedure(), nameEndProcedure, mModifiedGlobals);
				}
			} else if (trace.getSymbol(i) instanceof Return) {
				// Nothing to do
			} else {
				transformulasToComputeSummaryFor.addLast(rv.getFormulaFromNonCallPos(i));
			}
		}
		return TransFormulaUtils.sequentialComposition(mLogger, mServices, mMgdScript, true, false,
				s_TransformSummaryToCNF, mXnfConversionTechnique, mSimplificationTechnique, transformulasToComputeSummaryFor);

	}




}
