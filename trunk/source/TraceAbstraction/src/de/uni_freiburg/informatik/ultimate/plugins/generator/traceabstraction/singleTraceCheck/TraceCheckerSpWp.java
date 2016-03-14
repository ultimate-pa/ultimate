/*
 * Copyright (C) 2013-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.BasicPredicateExplicitQuantifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.UnsatCores;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;

/**
 * Use unsat core, predicate transformer and live variable analsysis to
 * compute a sequence of interpolants.
 * @author Betim Musa, Matthias Heizmann
 *
 */
public class TraceCheckerSpWp extends InterpolatingTraceChecker {

	// Forward relevant predicates
	protected IPredicate[] m_InterpolantsFp;
	// Backward relevant predicates
	protected IPredicate[] m_InterpolantsBp;

	private final UnsatCores m_UnsatCores;
	private final boolean m_LiveVariables;
	private final static boolean m_useLiveVariablesInsteadOfRelevantVariables = false;
	private final static boolean m_CollectInformationAboutSizeOfPredicates = true;
	
	// We may post-process the forwards predicates, after the backwards predicates has been computed in order 
	// to potentially eliminate quantifiers. The idea is the following:
	// If there is a predicate p in the forwards predicates that contains quantifiers and there is an equivalent predicate p' in the backwards 
	// predicates that is quantifier-free, then we may replace p by p'.
	private final static boolean m_PostProcess_FP_Predicates = false;

	private final boolean m_ConstructForwardInterpolantSequence;
	private final boolean m_ConstructBackwardInterpolantSequence;

	private static final boolean s_TransformToCNF = true;

	private AnnotateAndAssertConjunctsOfCodeBlocks m_AnnotateAndAsserterConjuncts;
	private final PredicateTransformer m_PredicateTransformer;
	
	private int m_NonLiveVariablesFp = 0;
	private int m_NonLiveVariablesBp = 0;
	

	public TraceCheckerSpWp(IPredicate precondition, IPredicate postcondition,
			SortedMap<Integer, IPredicate> pendingContexts, NestedWord<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals, AssertCodeBlockOrder assertCodeBlocksIncrementally,
			UnsatCores unsatCores, boolean useLiveVariables, 
			IUltimateServiceProvider services, boolean computeRcfgProgramExecution, 
			PredicateUnifier predicateUnifier, INTERPOLATION interpolation, SmtManager smtManagerTc) {
		// superclass does feasibility check
		super(precondition, postcondition, pendingContexts, trace, smtManager, modifiedGlobals,
				assertCodeBlocksIncrementally, services, computeRcfgProgramExecution, predicateUnifier, smtManagerTc);
		m_UnsatCores = unsatCores;
		m_LiveVariables = useLiveVariables;
		switch (interpolation) {
		case ForwardPredicates:
			m_ConstructForwardInterpolantSequence = true;
			m_ConstructBackwardInterpolantSequence = false;
			break;
		case BackwardPredicates:
			m_ConstructForwardInterpolantSequence = false;
			m_ConstructBackwardInterpolantSequence = true;
			break;
		case FPandBP:
			m_ConstructForwardInterpolantSequence = true;
			m_ConstructBackwardInterpolantSequence = true;
			break;
		default:
			throw new UnsupportedOperationException("unsupportedInterpolation");
		}
		m_PredicateTransformer = new PredicateTransformer(m_SmtManager, m_ModifiedGlobals, m_Services);
		if (isCorrect() == LBool.UNSAT) {
			computeInterpolants(new AllIntegers(), interpolation);
		}
	}

	@Override
	protected TraceCheckerBenchmarkGenerator getBenchmarkGenerator() {
		return new TraceCheckerBenchmarkSpWpGenerator();
	}

	@Override
	public void computeInterpolants(Set<Integer> interpolatedPositions,
			INTERPOLATION interpolation) {
		m_TraceCheckerBenchmarkGenerator.start(TraceCheckerBenchmarkType.s_InterpolantComputation);
		try {
			computeInterpolantsUsingUnsatCore(interpolatedPositions);
		} catch (ToolchainCanceledException tce) {
			m_Logger.info("Timeout while computing interpolants");
			m_ToolchainCanceledException = tce;
		} finally {
			m_TraceCheckerBenchmarkGenerator.stop(TraceCheckerBenchmarkType.s_InterpolantComputation);
		}
		m_TraceCheckFinished = true;
	}

	public boolean forwardsPredicatesComputed() {
		return m_ConstructForwardInterpolantSequence;
	}

	public boolean backwardsPredicatesComputed() {
		return m_ConstructBackwardInterpolantSequence;
	}

	public IPredicate[] getForwardPredicates() {
		assert m_InterpolantsFp != null : "Forwards predicates not computed!";
		return m_InterpolantsFp;
	}


	public IPredicate[] getBackwardPredicates() {
		assert m_InterpolantsBp != null : "Backwards predicates not computed!";
		return m_InterpolantsBp;
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
	private ProcedureSummary computeProcedureSummary(NestedWord<CodeBlock> trace, TransFormula Call,
			TransFormula Return, TransFormula oldVarsAssignment, TransFormula globalVarsAssignment, 
			NestedFormulas<TransFormula, IPredicate> rv,
			int call_pos, int return_pos) {
		TransFormula summaryOfInnerStatements = computeSummaryForInterproceduralTrace(trace, rv, call_pos + 1,
				return_pos);
		TransFormula summaryWithCallAndReturn = TransFormula.sequentialCompositionWithCallAndReturn(
				m_SmtManager.getBoogie2Smt(), true, false, s_TransformToCNF, Call, 
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
	private TransFormula computeSummaryForInterproceduralTrace(NestedWord<CodeBlock> trace,
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
								m_SmtManager.getBoogie2Smt(), true, false, s_TransformToCNF, callTf, oldVarsAssignment,
								globalVarsAssignment, summaryBetweenCallAndReturn, returnTf,
								m_Logger, m_Services));
						i = returnPosition;
					} else {
						// If the position of the corresponding Return is >=
						// "end",
						// then we handle this case as a pending-call
						TransFormula summaryAfterPendingCall = computeSummaryForInterproceduralTrace(trace, rv, i + 1, end);
						String nameEndProcedure = ((ProgramPoint) trace.getSymbol(end).getTarget()).getProcedure();
						Set<BoogieVar> modifiableGlobalsOfEndProcedure = m_ModifiedGlobals.getModifiedBoogieVars(nameEndProcedure);
						return TransFormula.sequentialCompositionWithPendingCall(m_SmtManager.getBoogie2Smt(), true,
								false, s_TransformToCNF, transformulasToComputeSummaryFor,
								callTf, oldVarsAssignment, summaryAfterPendingCall,
								m_Logger, m_Services, modifiableGlobalsOfEndProcedure);
					}
				} else {
					TransFormula summaryAfterPendingCall = computeSummaryForInterproceduralTrace(trace, rv, i + 1, end);
					String nameEndProcedure = ((ProgramPoint) trace.getSymbol(end).getTarget()).getProcedure();
					Set<BoogieVar> modifiableGlobalsOfEndProcedure = m_ModifiedGlobals.getModifiedBoogieVars(nameEndProcedure);
					return TransFormula.sequentialCompositionWithPendingCall(m_SmtManager.getBoogie2Smt(), true, false,
							s_TransformToCNF, transformulasToComputeSummaryFor,
							callTf, oldVarsAssignment, summaryAfterPendingCall, m_Logger,
							m_Services, modifiableGlobalsOfEndProcedure);
				}
			} else if (trace.getSymbol(i) instanceof Return) {
				// Nothing to do
			} else {
				transformulasToComputeSummaryFor.addLast(rv.getFormulaFromNonCallPos(i));
			}
		}
		return TransFormula.sequentialComposition(m_Logger, m_Services, m_SmtManager.getBoogie2Smt(), true, false,
				s_TransformToCNF, transformulasToComputeSummaryFor.toArray(new TransFormula[0]));

	}

	/***
	 * Computes predicates (interpolants) for the statements of an infeasible
	 * trace specified by the given set. Depending on settings, there are only
	 * forward predicates, or only backward predicates or both of them computed
	 * {@see computeForwardRelevantPredicates,
	 * computeBackwardRelevantPredicates} <br>
	 * The predicates are computed using an unsatisfiable core of the
	 * corresponding infeasibility proof of the trace in the following way: <br>
	 * 1. Replace statements, which don't occur in the unsatisfiable core by the
	 * statement <code> assume(true) </code> <br>
	 * 2. Compute live variables. <br>
	 * 3. Compute predicates for the trace, where the non-relevant statements
	 * has been substituted by <code> assume(true) </code>.
	 * 
	 * @see LiveVariables
	 * @see PredicateTransformer
	 */
	private void computeInterpolantsUsingUnsatCore(Set<Integer> interpolatedPositions) {
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		Set<Term> unsatCore = new HashSet<Term>(
				Arrays.asList(m_TcSmtManager.getScript().getUnsatCore()));
		// unsat core obtained. We now pop assertion stack of solver. This
		// allows us to use solver e.g. for simplifications
		unlockSmtManager();
		
		{
			final int numberOfConjunctsInTrace = m_AnnotateAndAsserterConjuncts.getAnnotated2Original().keySet().size();
			final int numberOfConjunctsInUnsatCore;
			if (m_UnsatCores == UnsatCores.IGNORE) {
				numberOfConjunctsInUnsatCore = 0;
			} else {
				numberOfConjunctsInUnsatCore= unsatCore.size();
			}
			m_Logger.debug("Total number of conjuncts in trace: " + numberOfConjunctsInTrace);
			m_Logger.debug("Number of conjuncts in unsatisfiable core: " + unsatCore.size());
			((TraceCheckerBenchmarkSpWpGenerator) m_TraceCheckerBenchmarkGenerator).setConjunctsInSSA(
					numberOfConjunctsInTrace, numberOfConjunctsInUnsatCore);
		}

		
		NestedFormulas<TransFormula, IPredicate> rtf = constructRelevantTransFormulas(unsatCore);
		assert stillInfeasible(rtf) : "incorrect Unsatisfiable Core";

		
		final Set<BoogieVar>[] liveVariables;
		if (m_useLiveVariablesInsteadOfRelevantVariables) {
			// computation of live variables whose input is the original trace
			LiveVariables lvar = new LiveVariables(m_Nsb.getVariable2Constant(), m_Nsb.getConstants2BoogieVar(),
					m_Nsb.getIndexedVarRepresentative(), m_SmtManager, m_ModifiedGlobals);
			liveVariables = lvar.getLiveVariables();
		} else {
			// computation of live variables whose input takes the unsat core into a account (if applicable)
			RelevantVariables rvar = new RelevantVariables(rtf, m_ModifiedGlobals);
			liveVariables = rvar.getRelevantVariables();
		}

		int[] sizeOfPredicatesFP = null;
		int[] sizeOfPredicatesBP = null;


		if (m_ConstructForwardInterpolantSequence) {
			m_Logger.debug("Computing forward predicates...");
			try {
				computeForwardPredicates(liveVariables, rtf);
			} catch (ToolchainCanceledException tce) {
				throw new ToolchainCanceledException(getClass(), tce.getRunningTaskInfo() + " while constructing forward predicates");
			}
			assert TraceCheckerUtils.checkInterpolantsInductivityForward(m_InterpolantsFp, 
					m_Trace, m_Precondition, m_Postcondition, m_PendingContexts, "FP", 
					m_SmtManager, m_ModifiedGlobals, m_Logger) : "invalid Hoare triple in FP";
			m_TraceCheckerBenchmarkGenerator.reportSequenceOfInterpolants(m_InterpolantsFp);
			if (m_CollectInformationAboutSizeOfPredicates) {
				sizeOfPredicatesFP = m_SmtManager.computeDagSizeOfPredicates(m_InterpolantsFp);
			}
		}
		
		if (m_ConstructBackwardInterpolantSequence) {
			m_Logger.debug("Computing backward predicates...");
			try {
				computeBackwardPredicates(liveVariables, rtf);
			} catch (ToolchainCanceledException tce) {
				throw new ToolchainCanceledException(getClass(), tce.getRunningTaskInfo() + " while constructing backward predicates");
			}
			assert TraceCheckerUtils.checkInterpolantsInductivityBackward(m_InterpolantsBp, 
					m_Trace, m_Precondition, m_Postcondition, m_PendingContexts, "BP", 
					m_SmtManager, m_ModifiedGlobals, m_Logger) : "invalid Hoare triple in BP";
			m_TraceCheckerBenchmarkGenerator.reportSequenceOfInterpolants(m_InterpolantsBp);
			if (m_CollectInformationAboutSizeOfPredicates) {
				sizeOfPredicatesBP = m_SmtManager.computeDagSizeOfPredicates(m_InterpolantsBp);
			}
		}


		
		if (m_ConstructForwardInterpolantSequence && m_ConstructBackwardInterpolantSequence) {
			// Post-process forwards predicates			
			if (m_PostProcess_FP_Predicates) {
				for (int i = 0; i < m_InterpolantsFp.length; i++) {
					IPredicate p_old = m_InterpolantsFp[i];
					IPredicate p_new = m_PredicateUnifier.getOrConstructPredicate(p_old.getFormula(), p_old.getVars(), p_old.getProcedures());
					m_InterpolantsFp[i] = p_new;
				}
				if (m_CollectInformationAboutSizeOfPredicates) {
					sizeOfPredicatesFP = m_SmtManager.computeDagSizeOfPredicates(m_InterpolantsFp);
				}
			}
		}
		
		((TraceCheckerBenchmarkSpWpGenerator) super.m_TraceCheckerBenchmarkGenerator).setPredicateData(
				sizeOfPredicatesFP, sizeOfPredicatesBP, m_NonLiveVariablesFp, m_NonLiveVariablesBp);

		// Check the validity of the computed interpolants.
//		if (m_ConstructForwardInterpolantSequence && m_ConstructBackwardInterpolantSequence) {
//			checkSPImpliesWP(m_InterpolantsFp, m_InterpolantsBp);
//		}
		if (m_ConstructForwardInterpolantSequence && m_ConstructBackwardInterpolantSequence) {
			selectListOFPredicatesFromBothTypes();
		} else if (m_ConstructForwardInterpolantSequence) {
			m_Interpolants = m_InterpolantsFp;
		} else if (m_ConstructBackwardInterpolantSequence) {
			m_Interpolants = m_InterpolantsBp;
		} else {
			throw new AssertionError("illegal choice");
		}
	}

	/**
	 * Construct representation of the trace formula that contains only the
	 * conjuncts that occur in the unsat core.
	 */
	private NestedFormulas<TransFormula, IPredicate> constructRelevantTransFormulas(Set<Term> unsatCore) {
		final NestedFormulas<TransFormula, IPredicate> rtf;
		if (m_UnsatCores == UnsatCores.IGNORE) {
			rtf = new DefaultTransFormulas(m_Trace, m_Precondition, m_Postcondition, m_PendingContexts,
					m_ModifiedGlobals, false);
		} else if (m_UnsatCores == UnsatCores.STATEMENT_LEVEL) {
			boolean[] localVarAssignmentAtCallInUnsatCore = new boolean[m_Trace.length()];
			boolean[] oldVarAssignmentAtCallInUnsatCore = new boolean[m_Trace.length()];
			// Filter out the statements, which doesn't occur in the unsat core.
			Set<CodeBlock> codeBlocksInUnsatCore = filterOutIrrelevantStatements(m_Trace, unsatCore,
					localVarAssignmentAtCallInUnsatCore, oldVarAssignmentAtCallInUnsatCore);
			rtf = new RelevantTransFormulas(m_Trace, m_Precondition, m_Postcondition, m_PendingContexts,
					codeBlocksInUnsatCore, m_ModifiedGlobals, localVarAssignmentAtCallInUnsatCore,
					oldVarAssignmentAtCallInUnsatCore, m_SmtManager);
		} else if (m_UnsatCores == UnsatCores.CONJUNCT_LEVEL) {
			rtf = new RelevantTransFormulas(m_Trace, m_Precondition, m_Postcondition, m_PendingContexts,
					unsatCore, m_ModifiedGlobals, m_SmtManager, m_AAA, m_AnnotateAndAsserterConjuncts);
		} else {
			throw new AssertionError("unknown case:" + m_UnsatCores);
		}
		return rtf;
	}

	/***
	 * Selects a list of predicates from the predicates computed via strongest
	 * post-condition and the weakest precondition, such that the number of
	 * predicates containing quantifiers is minimized and a mix-up of the two
	 * types is avoided. (If the predicates are mixed-up, they may get
	 * non-inductive.) Predicates are selected in the following way: (TODO:)
	 * 
	 */
	private void selectListOFPredicatesFromBothTypes() {
		assert m_InterpolantsFp.length == m_InterpolantsBp.length;
		m_Interpolants = new IPredicate[m_InterpolantsBp.length];
		int i = 0; // position of predicate computed by strongest post-condition
		int j = m_InterpolantsBp.length; // position of predicate computed by
		// weakest precondition
		while (i != j) {
			if (!(m_InterpolantsBp[j - 1] instanceof BasicPredicateExplicitQuantifier)) {
				m_Interpolants[j - 1] = m_InterpolantsBp[j - 1];
				j--;
			} else if (!(m_InterpolantsFp[i] instanceof BasicPredicateExplicitQuantifier)) {
				m_Interpolants[i] = m_InterpolantsFp[i];
				i++;
			} else {
				int numOfQuantifiedVarsInFp = ((BasicPredicateExplicitQuantifier) m_InterpolantsFp[i])
						.getQuantifiedVariables().size();
				int numOfQuantifiedVarsInBp = ((BasicPredicateExplicitQuantifier) m_InterpolantsBp[j - 1])
						.getQuantifiedVariables().size();
				if (numOfQuantifiedVarsInFp < numOfQuantifiedVarsInBp) {
					m_Interpolants[i] = m_InterpolantsFp[i];
					i++;
				} else {
					m_Interpolants[j - 1] = m_InterpolantsBp[j - 1];
					j--;
				}
			}
		}
	}

	/**
	 * Checks whether the trace consisting of only relevant statements is still
	 * infeasible. This check is desired, when we use unsatisfiable cores of
	 * finer granularity.
	 */
	private boolean stillInfeasible(NestedFormulas<TransFormula, IPredicate> rv) {
		TraceChecker tc = new TraceChecker(rv.getPrecondition(), rv.getPostcondition(),
				new TreeMap<Integer, IPredicate>(), rv.getTrace(), m_SmtManager, m_ModifiedGlobals, rv,
				AssertCodeBlockOrder.NOT_INCREMENTALLY, m_Services, false, true);
		if (tc.getToolchainCancelledExpection() != null) {
			throw tc.getToolchainCancelledExpection();
		}
		boolean result = (tc.isCorrect() == LBool.UNSAT);
		return result;
	}

	/**
	 * Select the statements from the given trace, which are contained in the
	 * unsatisfiable core. These statements contribute to the unsatisfiability
	 * of the trace, and therefore only these are important for the computations
	 * done afterwards.
	 */
	private Set<CodeBlock> filterOutIrrelevantStatements(NestedWord<CodeBlock> trace, Set<Term> unsat_coresAsSet,
			boolean[] localVarAssignmentAtCallInUnsatCore, boolean[] oldVarAssignmentAtCallInUnsatCore) {
		Set<CodeBlock> codeBlocksInUnsatCore = new HashSet<CodeBlock>();
		for (int i = 0; i < trace.length(); i++) {
			if (!trace.isCallPosition(i)
					&& unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getFormulaFromNonCallPos(i))) {
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			} else if (trace.isCallPosition(i)
					&& (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getGlobalVarAssignment(i)) || unsat_coresAsSet
							.contains(m_AAA.getAnnotatedSsa().getOldVarAssignment(i)))) {
				// The upper condition checks, whether the globalVarAssignments
				// is in unsat core, now check whether the local variable
				// assignments
				// is in unsat core, if it is Call statement
				if (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getLocalVarAssignment(i))) {
					localVarAssignmentAtCallInUnsatCore[i] = true;
				}
				if (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getOldVarAssignment(i))) {
					oldVarAssignmentAtCallInUnsatCore[i] = true;
				}
				// Add the globalVarAssignments to the unsat_core, if it is a
				// Call statement, otherwise it adds
				// the statement
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			} else {
				if (trace.getSymbol(i) instanceof Call) {
					if (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getLocalVarAssignment(i))) {
						localVarAssignmentAtCallInUnsatCore[i] = true;
					}
				}
			}
		}
		return codeBlocksInUnsatCore;
	}

	private void computeForwardPredicates(Set<BoogieVar>[] relevantVars,
			NestedFormulas<TransFormula, IPredicate> rv) {
		m_InterpolantsFp = new IPredicate[m_Trace.length() - 1];
		InterpolantsPreconditionPostcondition ipp = 
				new InterpolantsPreconditionPostcondition(m_Precondition,m_Postcondition, m_InterpolantsFp);

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
				final IPredicate projected;
				Set<TermVariable> nonLiveVars = computeIrrelevantVariables(relevantVars[i+1], sp);
				m_NonLiveVariablesFp += nonLiveVars.size();
				if (m_LiveVariables) {
					projected = m_SmtManager.constructPredicate(sp.getFormula(), 
							QuantifiedFormula.EXISTS, nonLiveVars);
				} else {
					projected = sp;
				}
				m_InterpolantsFp[i] = m_PredicateUnifier.getOrConstructPredicate(
						projected.getFormula(), projected.getVars(), projected.getProcedures());
//				if (m_CollectInformationAboutQuantifiedPredicates) {
//					IPredicate p = getForwardPredicateAtPosition(i, tracePrecondition, false);
//					if (p != null && p instanceof BasicPredicateExplicitQuantifier) {
//						numberOfQuantifiedPredicates[0]++;
//					}
//					p = getForwardPredicateAtPosition(i, tracePrecondition, true);
//					if (p != null && p instanceof BasicPredicateExplicitQuantifier) {
//						numberOfQuantifiedPredicates[1]++;
//					}
//				}
			}
	}
	
	
	private void computeBackwardPredicates(Set<BoogieVar>[] relevantVars,
			NestedFormulas<TransFormula, IPredicate> rv) {

		m_InterpolantsBp = new IPredicate[m_Trace.length()-1];
		InterpolantsPreconditionPostcondition ipp = 
				new InterpolantsPreconditionPostcondition(m_Precondition,m_Postcondition, m_InterpolantsBp);

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
					callerPredicatesComputed.put(
							callPos,
							m_PredicateUnifier.getOrConstructPredicate(callerPred.getFormula(),
									callerPred.getVars(), callerPred.getProcedures()));
				}
				wp = m_PredicateTransformer.weakestPrecondition(
						successor, callerPred, returnTf, callLocalVarsAssignment,
						globalVarsAssignments, oldVarAssignments, modifiableGlobals,
						varsOccurringBetweenCallAndReturn);
			} else {
				wp = m_PredicateTransformer.weakestPrecondition(
						successor, rv.getFormulaFromNonCallPos(i));
			}
			final IPredicate projected;
			Set<TermVariable> nonLiveVars = computeIrrelevantVariables(relevantVars[i], wp);
			if (m_LiveVariables) {
				projected = m_SmtManager.constructPredicate(wp.getFormula(), 
						QuantifiedFormula.FORALL, nonLiveVars);
				m_NonLiveVariablesBp += nonLiveVars.size();
			} else {
				projected = wp;
			}
			m_InterpolantsBp[i-1] = m_PredicateUnifier.getOrConstructPredicate(
					projected.getFormula(), projected.getVars(), projected.getProcedures());
			
//				if (m_CollectInformationAboutQuantifiedPredicates) {
//					if (wp != null && wp instanceof BasicPredicateExplicitQuantifier) {
//						numberOfQuantifiedPredicates[2]++;
//					}
//					if (bp instanceof BasicPredicateExplicitQuantifier) {
//						numberOfQuantifiedPredicates[3]++;
//					}
//				}
		}
	}
	
	
	/**
	 * Compute the irrelevant variables of the given predicate p. A variable is
	 * irrelevant, if it isn't contained in the given set of relevantVars.
	 * 
	 * @see LiveVariables
	 */
	private Set<TermVariable> computeIrrelevantVariables(Set<BoogieVar> relevantVars, IPredicate p) {
		Set<TermVariable> result = new HashSet<TermVariable>();
		for (BoogieVar bv : p.getVars()) {
			if (!relevantVars.contains(bv)) {
				result.add(bv.getTermVariable());
			}
		}
		return result;
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

	/***
	 * Check for each predicate computed via the strongest post-condition,
	 * whether it implies the predicate computed via weakest precondition. This
	 * check is desired, when predicates are computed twice (once via strongest
	 * post, and once via weakest pre-condition). It ensures the correctness of
	 * the predicates.
	 */
	private void checkSPImpliesWP(IPredicate[] interpolantsSP, IPredicate[] interpolantsWP) {
		m_Logger.debug("Checking implication of SP and WP...");
		for (int i = 0; i < interpolantsSP.length; i++) {
			LBool result = m_SmtManager.isCovered(interpolantsSP[i], interpolantsWP[i]);
			m_Logger.debug("SP {" + interpolantsSP[i] + "} ==> WP {" + interpolantsWP[i] + "} is "
					+ (result == LBool.UNSAT ? "valid" : (result == LBool.SAT ? "not valid" : result)));
			assert (result == LBool.UNSAT || result == LBool.UNKNOWN) : "checkSPImpliesWP failed";
		}
	}

	@Override
	protected AnnotateAndAssertCodeBlocks getAnnotateAndAsserterCodeBlocks(NestedFormulas<Term, Term> ssa) {
		if (m_AnnotateAndAsserterConjuncts == null) {
			m_AnnotateAndAsserterConjuncts = new AnnotateAndAssertConjunctsOfCodeBlocks(m_TcSmtManager, ssa,
					m_NestedFormulas, m_Logger, m_SmtManager);
		}
		return m_AnnotateAndAsserterConjuncts;
	}


	public static class TraceCheckerSpWpBenchmarkType extends TraceCheckerBenchmarkType implements IStatisticsType {

		private static TraceCheckerSpWpBenchmarkType s_Instance = new TraceCheckerSpWpBenchmarkType();

		protected final static String s_SizeOfPredicatesFP = "SizeOfPredicatesFP";
		protected final static String s_SizeOfPredicatesBP = "SizeOfPredicatesBP";
		protected final static String s_NumberOfNonLivePredicateFP = "NumberOfNonLivePredicateFP";
		protected final static String s_NumberOfNonLivePredicateBP = "NumberOfNonLivePredicateBP";
		protected final static String s_ConjunctsInSSA = "Conjuncts in SSA";
		protected final static String s_ConjunctsInUnsatCore = "Conjuncts in UnsatCore";

		public static TraceCheckerSpWpBenchmarkType getInstance() {
			return s_Instance;
		}

		@Override
		public Collection<String> getKeys() {
			ArrayList<String> result = new ArrayList<String>();
			for (String key : super.getKeys()) {
				result.add(key);
			}
			result.add(s_SizeOfPredicatesFP);
			result.add(s_SizeOfPredicatesBP);
			result.add(s_NumberOfNonLivePredicateFP);
			result.add(s_NumberOfNonLivePredicateBP);
			result.add(s_ConjunctsInSSA);
			result.add(s_ConjunctsInUnsatCore);
			return result;
		}

		@Override
		public Object aggregate(String key, Object value1, Object value2) {
			switch (key) {
			case s_SizeOfPredicatesFP:
			case s_SizeOfPredicatesBP:
				long size1 = (long) value1;
				long size2 = (long) value2;
				long result = size1 + size2;
				return result;
			case s_NumberOfNonLivePredicateFP:
			case s_NumberOfNonLivePredicateBP:
			case s_ConjunctsInSSA:
			case s_ConjunctsInUnsatCore: {
				return (Integer) value1 + (Integer) value2;
			}
			default:
				return super.aggregate(key, value1, value2);
			}
		}

		@Override
		public String prettyprintBenchmarkData(IStatisticsDataProvider benchmarkData) {
			StringBuilder sb = new StringBuilder();
			sb.append(super.prettyprintBenchmarkData(benchmarkData));
			sb.append("\t");
			sb.append(s_ConjunctsInSSA).append(": ");
			int conjunctsSSA = (int) benchmarkData.getValue(s_ConjunctsInSSA);
			sb.append(conjunctsSSA);
			sb.append(" ");
			sb.append(s_ConjunctsInUnsatCore).append(": ");
			int conjunctsUC = (int) benchmarkData.getValue(s_ConjunctsInUnsatCore);
			sb.append(conjunctsUC);
			sb.append("\t");
			long sizeOfPredicatesFP = (long) benchmarkData.getValue(s_SizeOfPredicatesFP);
			sb.append("Size of predicates FP: " + sizeOfPredicatesFP + " ");
			long sizeOfPredicatesBP = (long) benchmarkData.getValue(s_SizeOfPredicatesBP);
			sb.append("Size of predicates BP: " + sizeOfPredicatesBP + " ");
			int numberOfNonLivePredicateFP = (int) benchmarkData.getValue(s_NumberOfNonLivePredicateFP);
			sb.append("Non-live variables FP: " + numberOfNonLivePredicateFP + " ");
			int numberOfNonLivePredicateBP = (int) benchmarkData.getValue(s_NumberOfNonLivePredicateBP);
			sb.append("Non-live variables BP: " + numberOfNonLivePredicateBP + " ");
			return sb.toString();
		}
	}

	/**
	 * Stores benchmark data about the usage of TraceCheckers. E.g., number and
	 * size of predicates obtained via interpolation.
	 */
	public class TraceCheckerBenchmarkSpWpGenerator extends TraceCheckerBenchmarkGenerator implements
	IStatisticsDataProvider {
		// m_NumberOfQuantifierFreePredicates[0] : Sum of the DAG-Size of
		// predicates computed via FP
		// m_NumberOfQuantifierFreePredicates[1] : Sum of the DAG-Size of
		// predicates computed via BP
		private long[] m_SizeOfPredicates = new long[2];
		
		private int m_NumberOfNonLiveVariablesFP = -1;
		private int m_NumberOfNonLiveVariablesBP = -1;

		private int m_ConjunctsInSSA;
		private int m_ConjunctsInUC;

		@Override
		public String[] getStopwatches() {
			return super.getStopwatches();
		}

		public void setPredicateData(int[] sizeOfPredicatesFP, int[] sizeOfPredicatesBP,
				int numberOfNonLiveVariablesFP, int numberOfNonLiveVariablesBP) {
			m_SizeOfPredicates = new long[2];
			if (sizeOfPredicatesFP != null) {
				m_SizeOfPredicates[0] = getSumOfIntArray(sizeOfPredicatesFP);
			} else {
				m_SizeOfPredicates[0] = 0;
			}
			if (sizeOfPredicatesBP != null) {
				m_SizeOfPredicates[1] = getSumOfIntArray(sizeOfPredicatesBP);
			} else {
				m_SizeOfPredicates[1] = 0;
			}
			m_NumberOfNonLiveVariablesFP = numberOfNonLiveVariablesFP;
			m_NumberOfNonLiveVariablesBP = numberOfNonLiveVariablesBP;
		}

		public void setConjunctsInSSA(int conjunctsInSSA, int conjunctsInUC) {
			assert m_ConjunctsInSSA == 0 : "have already been set";
			assert m_ConjunctsInUC == 0 : "have already been set";
			m_ConjunctsInSSA = conjunctsInSSA;
			m_ConjunctsInUC = conjunctsInUC;
		}

		private long getSumOfIntArray(int[] arr) {
			long sum = 0;
			for (int i = 0; i < arr.length; i++) {
				sum += arr[i];
			}
			return sum;
		}

		@Override
		public Collection<String> getKeys() {
			return TraceCheckerSpWpBenchmarkType.getInstance().getKeys();
		}

		@Override
		public Object getValue(String key) {
			switch (key) {
			case TraceCheckerSpWpBenchmarkType.s_ConjunctsInSSA:
				return m_ConjunctsInSSA;
			case TraceCheckerSpWpBenchmarkType.s_ConjunctsInUnsatCore:
				return m_ConjunctsInUC;
			case TraceCheckerSpWpBenchmarkType.s_SizeOfPredicatesFP:
				return m_SizeOfPredicates[0];
			case TraceCheckerSpWpBenchmarkType.s_SizeOfPredicatesBP:
				return m_SizeOfPredicates[1];
			case TraceCheckerSpWpBenchmarkType.s_NumberOfNonLivePredicateFP:
				return m_NumberOfNonLiveVariablesFP;
			case TraceCheckerSpWpBenchmarkType.s_NumberOfNonLivePredicateBP:
				return m_NumberOfNonLiveVariablesBP;
			default:
				return super.getValue(key);
			}
		}

		@Override
		public TraceCheckerSpWpBenchmarkType getBenchmarkType() {
			return TraceCheckerSpWpBenchmarkType.getInstance();
		}
	}

}
