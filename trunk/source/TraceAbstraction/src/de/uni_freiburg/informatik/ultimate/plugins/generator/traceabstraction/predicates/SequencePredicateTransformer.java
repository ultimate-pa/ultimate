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

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.VariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class SequencePredicateTransformer {
	private final ModifiableGlobalVariableManager m_ModifiedGlobals;
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	private final Boogie2SMT m_Boogie2SMT;
	
	private final PredicateTransformer m_PredicateTransformer;
	private final NestedWord<? extends IAction> m_Trace;
	private IPredicate m_Precondition;
	private IPredicate m_Postcondition;
	protected final SortedMap<Integer, IPredicate> m_PendingContexts;
	
	private static final boolean s_TransformSummaryToCNF = true;

	public SequencePredicateTransformer(PredicateFactory predicateFactory, 
			VariableManager variableManager, Script script,
			Boogie2SMT boogie2smt,
			ModifiableGlobalVariableManager modifiableGlobalVariableManager,
			IUltimateServiceProvider services, NestedWord<? extends IAction> trace, 
			IPredicate precondition, IPredicate postcondition, 
			SortedMap<Integer, IPredicate> pendingContexts) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Boogie2SMT = boogie2smt;
		m_ModifiedGlobals = modifiableGlobalVariableManager;
		m_PredicateTransformer = new PredicateTransformer(predicateFactory, 
				variableManager, script, modifiableGlobalVariableManager, services);
		m_Trace = trace;
		m_Precondition = precondition;
		m_Postcondition = postcondition;
		m_PendingContexts = pendingContexts;
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
	
	
	
	public InterpolantsPreconditionPostcondition computeForwardPredicates(
			NestedFormulas<TransFormula, IPredicate> rv, List<PredicatePostprocessor> postprocs) {
		IPredicate[] interpolantsFp = new IPredicate[m_Trace.length() - 1];
		InterpolantsPreconditionPostcondition ipp = 
				new InterpolantsPreconditionPostcondition(m_Precondition, m_Postcondition, Arrays.asList(interpolantsFp));

		for (int i = 0; i < m_Trace.length() - 1; i++) {
			final IPredicate predecessor = ipp.getInterpolant(i); 
			final IPredicate sp;
			if (m_Trace.getSymbol(i) instanceof Call) {
				final Call call = (Call) m_Trace.getSymbol(i); 
				final String calledMethod = call.getCallStatement().getMethodName();
				final Set<BoogieVar> modifiedGlobals = m_ModifiedGlobals.getModifiedBoogieVars(calledMethod);
				if (m_Trace.isPendingCall(i)) {
					sp = m_PredicateTransformer.strongestPostconditionCall(
							predecessor, rv.getLocalVarAssignment(i),
							rv.getGlobalVarAssignment(i), rv.getOldVarAssignment(i),
							modifiedGlobals);
				} else {
					sp = m_PredicateTransformer.weakLocalPostconditionCall(
							predecessor,
							rv.getGlobalVarAssignment(i),
							modifiedGlobals);
				}
			} else if (m_Trace.getSymbol(i) instanceof Return) {
				final IPredicate callerPred;
				final TransFormula callGlobalVarsAssignment;
				final TransFormula callOldVarsAssignment;
				final TransFormula callLocalVarsAssignment;
				if (m_Trace.isPendingReturn(i)) {
					callerPred = m_PendingContexts.get(i);
					callOldVarsAssignment = rv.getOldVarAssignment(i);
					callGlobalVarsAssignment = null;
					callLocalVarsAssignment = rv.getLocalVarAssignment(i);
				} else {
					int callPos = m_Trace.getCallPosition(i);
					assert callPos >= 0 && callPos <= i : "Bad call position!";
					callerPred = ipp.getInterpolant(callPos);
					callGlobalVarsAssignment = rv.getGlobalVarAssignment(callPos);
					callOldVarsAssignment = null;
					callLocalVarsAssignment = rv.getLocalVarAssignment(callPos);
				}
				final TransFormula returnTransFormula = rv.getFormulaFromNonCallPos(i);
				sp = m_PredicateTransformer.strongestPostcondition(
						predecessor, callerPred,
						returnTransFormula, callLocalVarsAssignment, 
						callGlobalVarsAssignment, callOldVarsAssignment);
			} else {
				sp = m_PredicateTransformer.strongestPostcondition(
						predecessor,
						rv.getFormulaFromNonCallPos(i));
			}
			interpolantsFp[i] = applyPostprocessors(postprocs, i+1, sp);
		}
		return ipp;
	}
	
	

	
	
	public InterpolantsPreconditionPostcondition computeBackwardPredicates(
			NestedFormulas<TransFormula, IPredicate> rv, List<PredicatePostprocessor> postprocs) {

		IPredicate[] interpolantsBp = new IPredicate[m_Trace.length()-1];
		InterpolantsPreconditionPostcondition ipp = 
				new InterpolantsPreconditionPostcondition(m_Precondition,m_Postcondition, Arrays.asList(interpolantsBp));

		// Contains the predicates, which are computed during a Return with
		// the second method, where the callerPred
		// is computed as wp(returnerPred, summaryOfCalledProcedure).
		Map<Integer, IPredicate> callerPredicatesComputed = new HashMap<Integer, IPredicate>();
		for (int i = m_Trace.length()-1; i >= 1; i--) {
			final IPredicate wp;
			IPredicate successor = ipp.getInterpolant(i+1);
			if (m_Trace.getSymbol(i) instanceof Call) {
				if (m_Trace.isPendingCall(i)) {
					final Call call = (Call) m_Trace.getSymbol(i); 
					final String calledMethod = call.getCallStatement().getMethodName();
					final Set<BoogieVar> modifiedGlobals = m_ModifiedGlobals.getModifiedBoogieVars(calledMethod);
					wp = m_PredicateTransformer.weakestPrecondition(
							successor,
							rv.getLocalVarAssignment(i), rv.getGlobalVarAssignment(i),
							rv.getOldVarAssignment(i), modifiedGlobals);
				} else {
					wp = callerPredicatesComputed.get(i);
					assert wp != null : "must have already been computed";
					//						wp = m_SmtManager.renameVarsOfOtherProcsToFreshVars(callerPredicatesComputed.get(i + 1),
					//								((Call) trace.getSymbol(i + 1)).getPreceedingProcedure());
					//						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(wp.getFormula(), wp.getVars(),
					//								wp.getProcedures());
				}
			} else if (m_Trace.getSymbol(i) instanceof Return) {
				final IPredicate callerPred;
				final TransFormula globalVarsAssignments;
				final TransFormula oldVarAssignments;
				final TransFormula callLocalVarsAssignment;
				final TransFormula returnTf = rv.getFormulaFromNonCallPos(i);
				final Return returnCB = (Return) m_Trace.getSymbol(i);
				final String calledMethod = returnCB.getCallStatement().getMethodName();
				final Set<BoogieVar> modifiableGlobals = m_ModifiedGlobals.getModifiedBoogieVars(calledMethod);

				final Set<BoogieVar> varsOccurringBetweenCallAndReturn;
				if (m_Trace.isPendingReturn(i)) {
					callerPred = m_PendingContexts.get(new Integer(i));
					// we may get the local variable assignment (pending
					// context)
					// by requesting it at the position of the
					// pending-return.
					callLocalVarsAssignment = rv.getLocalVarAssignment(i);
					oldVarAssignments = rv.getOldVarAssignment(i);
					globalVarsAssignments = rv.getGlobalVarAssignment(i);
					// this is probably not yet supported
					varsOccurringBetweenCallAndReturn = null;
				} else {
					int callPos = m_Trace.getCallPosition(i);
					assert callPos >= 0 && callPos <= i : "Bad call position!";
					callLocalVarsAssignment = rv.getLocalVarAssignment(callPos);
					globalVarsAssignments = rv.getGlobalVarAssignment(callPos);
					oldVarAssignments = rv.getOldVarAssignment(callPos);
					final ProcedureSummary summary = computeProcedureSummary(
							m_Trace, callLocalVarsAssignment, returnTf, 
							oldVarAssignments, globalVarsAssignments, rv, callPos, i);
					varsOccurringBetweenCallAndReturn = summary.computeVariableInInnerSummary();
					callerPred = m_PredicateTransformer.weakestPrecondition(
							successor,
							summary.getWithCallAndReturn());
					callerPredicatesComputed.put(callPos, callerPred);
				}
				wp = m_PredicateTransformer.weakestPrecondition(
						successor, callerPred, returnTf, callLocalVarsAssignment,
						globalVarsAssignments, oldVarAssignments, modifiableGlobals,
						varsOccurringBetweenCallAndReturn);
			} else {
				wp = m_PredicateTransformer.weakestPrecondition(
						successor, rv.getFormulaFromNonCallPos(i));
			}
			interpolantsBp[i-1] = applyPostprocessors(postprocs, i, wp);
			
		}
		return ipp;
	}


	private IPredicate applyPostprocessors(
			List<PredicatePostprocessor> postprocs, int i, final IPredicate pred) {
		IPredicate postprocessed = pred;
		for (PredicatePostprocessor postproc : postprocs) {
			postprocessed = postproc.postprocess(postprocessed, i);
		}
		return postprocessed;
	}
	
	
	private class ProcedureSummary {
		private final TransFormula m_WithCallAndReturn;
		private final TransFormula m_WithoutCallAndReturn;

		public ProcedureSummary(TransFormula withCallAndReturn, TransFormula withoutCallAndReturn) {
			super();
			m_WithCallAndReturn = withCallAndReturn;
			m_WithoutCallAndReturn = withoutCallAndReturn;
		}

		public TransFormula getWithCallAndReturn() {
			return m_WithCallAndReturn;
		}

		public TransFormula getWithoutCallAndReturn() {
			return m_WithoutCallAndReturn;
		}

		/**
		 * Returns a set that contains all variables that occur in the summary
		 * without call and return.
		 */
		public Set<BoogieVar> computeVariableInInnerSummary() {
			return new Set<BoogieVar>() {

				@Override
				public boolean add(BoogieVar e) {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean addAll(Collection<? extends BoogieVar> c) {
					throw new UnsupportedOperationException();
				}

				@Override
				public void clear() {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean contains(Object o) {
					return m_WithoutCallAndReturn.getInVars().containsKey(o)
							|| m_WithoutCallAndReturn.getOutVars().containsKey(o);
				}

				@Override
				public boolean containsAll(Collection<?> c) {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean isEmpty() {
					throw new UnsupportedOperationException();
				}

				@Override
				public Iterator<BoogieVar> iterator() {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean remove(Object o) {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean removeAll(Collection<?> c) {
					throw new UnsupportedOperationException();
				}

				@Override
				public boolean retainAll(Collection<?> c) {
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
				public <T> T[] toArray(T[] a) {
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
	private ProcedureSummary computeProcedureSummary(NestedWord<? extends IAction> trace, TransFormula Call,
			TransFormula Return, TransFormula oldVarsAssignment, TransFormula globalVarsAssignment, 
			NestedFormulas<TransFormula, IPredicate> rv,
			int call_pos, int return_pos) {
		TransFormula summaryOfInnerStatements = computeSummaryForInterproceduralTrace(trace, rv, call_pos + 1,
				return_pos);
		TransFormula summaryWithCallAndReturn = TransFormula.sequentialCompositionWithCallAndReturn(
				m_Boogie2SMT, true, false, s_TransformSummaryToCNF, Call, 
				oldVarsAssignment, globalVarsAssignment,
				summaryOfInnerStatements, Return, m_Logger, m_Services);
		return new ProcedureSummary(summaryWithCallAndReturn, summaryOfInnerStatements);
	}

	/**
	 * Computes a summary for the given trace, but only for the statements from
	 * position "start" to position "end".
	 * 
	 * @return - a summary for the statements from the given trace from position
	 *         "start" to position "end"
	 */
	private TransFormula computeSummaryForInterproceduralTrace(NestedWord<? extends IAction> trace,
			NestedFormulas<TransFormula, IPredicate> rv, int start, int end) {
		LinkedList<TransFormula> transformulasToComputeSummaryFor = new LinkedList<TransFormula>();
		for (int i = start; i < end; i++) {
			if (trace.getSymbol(i) instanceof Call) {
				TransFormula callTf = rv.getLocalVarAssignment(i);
				TransFormula oldVarsAssignment = rv.getOldVarAssignment(i);
				TransFormula globalVarsAssignment = rv.getGlobalVarAssignment(i);
				if (!trace.isPendingCall(i)) {
					// Case: non-pending call
					// Compute a summary for Call and corresponding Return, but
					// only if the position of the corresponding
					// Return is smaller than the position "end"
					int returnPosition = trace.getReturnPosition(i);
					if (returnPosition < end) {
						// 1. Compute a summary for the statements between this
						// non-pending Call
						// and the corresponding Return recursively
						TransFormula summaryBetweenCallAndReturn = computeSummaryForInterproceduralTrace(trace, rv,
								i + 1, returnPosition);
						TransFormula returnTf = rv.getFormulaFromNonCallPos(returnPosition);
						transformulasToComputeSummaryFor.addLast(TransFormula.sequentialCompositionWithCallAndReturn(
								m_Boogie2SMT, true, false, s_TransformSummaryToCNF, callTf, oldVarsAssignment,
								globalVarsAssignment, summaryBetweenCallAndReturn, returnTf,
								m_Logger, m_Services));
						i = returnPosition;
					} else {
						// If the position of the corresponding Return is >=
						// "end",
						// then we handle this case as a pending-call
						TransFormula summaryAfterPendingCall = computeSummaryForInterproceduralTrace(trace, rv, i + 1, end);
						String nameEndProcedure = trace.getSymbol(end).getSucceedingProcedure();
						Set<BoogieVar> modifiableGlobalsOfEndProcedure = m_ModifiedGlobals.getModifiedBoogieVars(nameEndProcedure);
						return TransFormula.sequentialCompositionWithPendingCall(m_Boogie2SMT, true,
								false, s_TransformSummaryToCNF, transformulasToComputeSummaryFor,
								callTf, oldVarsAssignment, summaryAfterPendingCall,
								m_Logger, m_Services, modifiableGlobalsOfEndProcedure);
					}
				} else {
					TransFormula summaryAfterPendingCall = computeSummaryForInterproceduralTrace(trace, rv, i + 1, end);
					String nameEndProcedure = trace.getSymbol(end).getSucceedingProcedure();
					Set<BoogieVar> modifiableGlobalsOfEndProcedure = m_ModifiedGlobals.getModifiedBoogieVars(nameEndProcedure);
					return TransFormula.sequentialCompositionWithPendingCall(m_Boogie2SMT, true, false,
							s_TransformSummaryToCNF, transformulasToComputeSummaryFor,
							callTf, oldVarsAssignment, summaryAfterPendingCall, m_Logger,
							m_Services, modifiableGlobalsOfEndProcedure);
				}
			} else if (trace.getSymbol(i) instanceof Return) {
				// Nothing to do
			} else {
				transformulasToComputeSummaryFor.addLast(rv.getFormulaFromNonCallPos(i));
			}
		}
		return TransFormula.sequentialComposition(m_Logger, m_Services, m_Boogie2SMT, true, false,
				s_TransformSummaryToCNF, transformulasToComputeSummaryFor.toArray(new TransFormula[0]));

	}




}
