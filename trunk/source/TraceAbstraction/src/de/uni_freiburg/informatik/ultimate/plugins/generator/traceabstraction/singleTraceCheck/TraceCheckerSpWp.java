package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.BasicPredicateExplicitQuantifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;

public class TraceCheckerSpWp extends TraceChecker {
	/*
	 * Settings for SVComp:
	 * m_useUnsatCore = true;
	 * m_useUnsatCoreOfFineGranularity = true;
	 * m_useLiveVariables = true;
	 * m_LogInformation = false;
	 * m_CollectInformationAboutQuantifiedPredicates = false;
	 * m_ComputeInterpolantsSp = true;
	 * m_ComputeInterpolantsFp = true;
	 * m_ComputeInterpolantsBp = false;
	 * m_ComputeInterpolantsWp = false;
	 */
	
	
	protected IPredicate[] m_InterpolantsSp;
	protected IPredicate[] m_InterpolantsWp;
	
	// Forward relevant predicates
	protected IPredicate[] m_InterpolantsFp;
	// Backward relevant predicates
	protected IPredicate[] m_InterpolantsBp;
	
	
	private final static boolean m_useUnsatCore = true;
	private final static boolean m_useUnsatCoreOfFineGranularity = true;
	private final static boolean m_useLiveVariables = true;
	private final static boolean m_LogInformation = true;
	private final static boolean m_CollectInformationAboutQuantifiedPredicates = true;
	private final static boolean m_CollectInformationAboutSizeOfPredicates = true;
	// m_NumberOfQuantifierFreePredicates[0] : #quantified predicates of SP
	// m_NumberOfQuantifierFreePredicates[1] : #quantified predicates of FP
	// m_NumberOfQuantifierFreePredicates[2] : #quantified predicates of WP
	// m_NumberOfQuantifierFreePredicates[3] : #quantified predicates of BP
	private int[] m_NumberOfQuantifiedPredicates;
	private int[] m_SizeOfPredicatesFP;
	private int[] m_SizeOfPredicatesBP;
	private boolean m_ComputeInterpolantsSp;
	private boolean m_ComputeInterpolantsFp;
	private boolean m_ComputeInterpolantsBp;
	private boolean m_ComputeInterpolantsWp;
	
	private static final boolean s_TransformToCNF = true;
	

	public TraceCheckerSpWp(IPredicate precondition, IPredicate postcondition,
			NestedWord<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals) {
		super(precondition, postcondition, null, trace, smtManager, modifiedGlobals);
		m_NumberOfQuantifiedPredicates = new int[4];
	}
	

	@Override
	public void computeInterpolants(Set<Integer> interpolatedPositions, 
			PredicateUnifier predicateUnifier, INTERPOLATION interpolation) {
		switch (interpolation) {
			case ForwardPredicates:
				m_ComputeInterpolantsSp = true;
				m_ComputeInterpolantsFp = true;
				m_ComputeInterpolantsWp = false;
				m_ComputeInterpolantsBp = false;
				break;
			case BackwardPredicates:
				m_ComputeInterpolantsSp = false;
				m_ComputeInterpolantsFp = false;
				m_ComputeInterpolantsWp = true;
				m_ComputeInterpolantsBp = true;
				break;
			case FPandBP:
				m_ComputeInterpolantsSp = true;
				m_ComputeInterpolantsFp = true;
				m_ComputeInterpolantsWp = true;
				m_ComputeInterpolantsBp = true;
				break;
			default:
				throw new UnsupportedOperationException("unsupportedInterpolation");
			}
		m_PredicateUnifier = predicateUnifier;
		if (m_useUnsatCore) {
			computeInterpolantsWithUsageOfUnsatCore(interpolatedPositions);
		} else {
			computeInterpolantsWithoutUsageOfUnsatCore(interpolatedPositions);
		}
	}
	
	private int[] getSizeOfPredicatesFP() {
		assert m_SizeOfPredicatesFP != null;
		return m_SizeOfPredicatesFP;
	}

	private int[] getSizeOfPredicatesBP() {
		assert m_SizeOfPredicatesBP != null;
		return m_SizeOfPredicatesBP;
	}

	public Integer getNumberOfQuantifiedPredicatesFP() {
		assert m_NumberOfQuantifiedPredicates != null;
		return m_NumberOfQuantifiedPredicates[1];
	}
	
	public Integer getNumberOfQuantifiedPredicatesBP() {
		assert m_NumberOfQuantifiedPredicates != null;
		return m_NumberOfQuantifiedPredicates[3];
	}


	public boolean forwardsPredicatesComputed() {
		return m_ComputeInterpolantsFp;
	}
	
	public boolean backwardsPredicatesComputed() {
		return m_ComputeInterpolantsBp;
	}
	
	public IPredicate getForwardPredicateAtPosition(int i) {
		assert i >= 0 && i < m_InterpolantsFp.length : ("The given position "+ i
				+ " is not a correct position. #Interpolants = " 
				+ m_InterpolantsFp.length);
		return m_InterpolantsFp[i];
	}
	
	public IPredicate getBackwardPredicateAtPosition(int i) {
		assert i >= 0 && i < m_InterpolantsBp.length : ("The given position "+ i + 
				" is not a correct position! #Interpolants = " + m_InterpolantsBp.length);
		return m_InterpolantsBp[i];
	}
	
	
	private IPredicate getBackwardPredicateAtPosition(int i, IPredicate tracePostcondition, boolean backwardPredicate) {
		if (i >= m_InterpolantsWp.length) {
			return tracePostcondition;
		} else {
			assert i >= 0;
			if (!backwardPredicate) 
				return m_InterpolantsWp[i];
			else
				return m_InterpolantsBp[i];
		}
	}
	
	
	private IPredicate getForwardPredicateAtPosition(int i, IPredicate tracePrecondition, boolean forwardPredicate) {
		if (i < 0) {
			return tracePrecondition;
		} else {
			assert i < m_InterpolantsSp.length;
			if (!forwardPredicate) 
				return m_InterpolantsSp[i];
			else
				return m_InterpolantsFp[i];
		}
	}
	
	/**
	 * Computes a summary of the procedure. The procedure consists (or is represented) by the Call statement, the Return statement 
	 * and the inner statements.
	 * @param trace - the inner statements of the procedure
	 * @param Call
	 * @param Return
	 * @param oldVarsAssignment
	 * @param rv
	 * @param call_pos
	 * @return
	 */
	private TransFormula computeProcedureSummary(NestedWord<CodeBlock> trace, TransFormula Call, 
			TransFormula Return, 
			TransFormula oldVarsAssignment,
			RelevantTransFormulas rv,
			int call_pos) {
		TransFormula summaryOfInnerStatements = computeSummaryForInterproceduralTrace(trace, rv, 0, trace.length());
		return TransFormula.sequentialCompositionWithCallAndReturn(m_SmtManager.getBoogie2Smt(), true, false, s_TransformToCNF, Call, oldVarsAssignment, summaryOfInnerStatements, Return);
	}
	
	/**
	 * Computes a summary for the given trace, but only for the statements from position "start" to position "end".
	 * @return - a summary for the statements from the given trace from position "start" to position "end"
	 */
	private TransFormula computeSummaryForInterproceduralTrace(NestedWord<CodeBlock> trace, RelevantTransFormulas rv, int start, int end) {
		LinkedList<TransFormula> transformulasToComputeSummaryFor = new LinkedList<TransFormula>();
		for (int i = start; i < end; i++) {
			if (trace.getSymbol(i) instanceof Call) {
				String proc = ((Call)trace.getSymbol(i)).getCallStatement().getMethodName();
				if (!trace.isPendingCall(i)) {
					// Case: non-pending call
					// Compute a summary for Call and corresponding Return, but only if the position of the corresponding
					// Return is smaller than the position "end"
					int returnPosition = trace.getReturnPosition(i);
					if (returnPosition < end) {
						// 1. Compute a summary for the statements between this non-pending Call
						// and the corresponding  Return recursively
						TransFormula summaryBetweenCallAndReturn = computeSummaryForInterproceduralTrace(trace,
								rv,
								i+1, returnPosition);
						/** FIXME: Here, we have to assign the original statements for Call and Return as parameters, because
						 the method {@link TransFormula.sequentialCompositionWithCallAndReturn} expects CodeBlocks and not
						 TransFormulas.
						 */
						transformulasToComputeSummaryFor.addLast(TransFormula.sequentialCompositionWithCallAndReturn(
								m_SmtManager.getBoogie2Smt(), true, false, s_TransformToCNF,
								trace.getSymbol(i).getTransitionFormula(),
								m_ModifiedGlobals.getOldVarsAssignment(proc), summaryBetweenCallAndReturn, 
								trace.getSymbol(returnPosition).getTransitionFormula()));
						i = returnPosition;
					} else {
						// If the position of the corresponding Return is >= "end", 
						// then we handle this case as a pending-call
						TransFormula summaryAfterPendingCall = computeSummaryForInterproceduralTrace(
								trace, rv,
								i+1,
								end);
						return TransFormula.sequentialCompositionWithPendingCall(m_SmtManager.getBoogie2Smt(), 
								true, false, s_TransformToCNF, transformulasToComputeSummaryFor.toArray(new TransFormula[0]),
								rv.getLocalVarAssignment(i), 
								m_ModifiedGlobals.getOldVarsAssignment(proc), summaryAfterPendingCall);
					}
				} else {
					TransFormula summaryAfterPendingCall = computeSummaryForInterproceduralTrace(
							trace, rv,
							i+1,
							end);
					return TransFormula.sequentialCompositionWithPendingCall(m_SmtManager.getBoogie2Smt(), 
							true, false, s_TransformToCNF, transformulasToComputeSummaryFor.toArray(new TransFormula[0]),
							rv.getLocalVarAssignment(i), 
							m_ModifiedGlobals.getOldVarsAssignment(proc), summaryAfterPendingCall);
				}
			} else if (trace.getSymbol(i) instanceof Return) {
				// Nothing to do
			} else {
				transformulasToComputeSummaryFor.addLast(rv.getFormulaFromNonCallPos(i));
			}
		}
		return TransFormula.sequentialComposition(m_SmtManager.getBoogie2Smt(), true, false,
				s_TransformToCNF,
				transformulasToComputeSummaryFor.toArray(new TransFormula[0]));
		
	}

	/***
 	 * TODO: Document this!
 	 * TODO: Split the code! 
 	 */
	private void computeInterpolantsWithUsageOfUnsatCore(Set<Integer> interpolatedPositions) {
		m_NumberOfQuantifiedPredicates = new int[4];
		
		Term[] unsat_core = m_SmtManager.getScript().getUnsatCore();
		
		Set<Term> unsat_coresAsSet = new HashSet<Term>(Arrays.asList(unsat_core));
		
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		m_PredicateUnifier.declarePredicate(tracePrecondition);
		m_PredicateUnifier.declarePredicate(tracePostcondition);
		NestedWord<CodeBlock> trace = m_Trace;
		unlockSmtManager();
		RelevantTransFormulas rv = null;
		
		if (m_LogInformation) {
			if (m_AAA instanceof AnnotateAndAsserterConjuncts) {
				int totalNumberOfConjunctsInTrace = ((AnnotateAndAsserterConjuncts)m_AAA).getAnnotated2Original().keySet().size();
				s_Logger.debug("Total number of conjuncts in trace: " +  totalNumberOfConjunctsInTrace);
				s_Logger.debug("Number of conjuncts in unsatisfiable core: " + unsat_coresAsSet.size());
			}
		}
		
		if (!m_useUnsatCoreOfFineGranularity) {
			boolean[] localVarAssignmentAtCallInUnsatCore = new boolean[trace.length()];
			boolean[] oldVarAssignmentAtCallInUnsatCore = new boolean[trace.length()];
			// Filter out the statements, which doesn't occur in the unsat core.
			Set<CodeBlock> codeBlocksInUnsatCore = filterOutIrrelevantStatements(trace, unsat_coresAsSet, 
					localVarAssignmentAtCallInUnsatCore, 
					oldVarAssignmentAtCallInUnsatCore);
			rv = new RelevantTransFormulas(trace,
					m_Precondition, m_Postcondition, m_PendingContexts,
					codeBlocksInUnsatCore,
					m_ModifiedGlobals,
					localVarAssignmentAtCallInUnsatCore,
					oldVarAssignmentAtCallInUnsatCore,
					m_SmtManager);
		} else {
			rv = new RelevantTransFormulas(trace,
					m_Precondition, m_Postcondition, m_PendingContexts,
					unsat_coresAsSet,
					m_ModifiedGlobals,
					m_SmtManager,
					(AnnotateAndAsserterConjuncts)m_AAA);
			assert stillInfeasible(rv);
		}
		Set<BoogieVar>[] relevantVarsToUseForFPBP = null;
		
		if (m_useLiveVariables) {
			LiveVariables lvar = new LiveVariables(m_Nsb.getVariable2Constant(), m_Nsb.getConstants2BoogieVar(),
					m_Nsb.getIndexedVarRepresentative(),
					m_SmtManager, m_ModifiedGlobals);
			relevantVarsToUseForFPBP = lvar.getLiveVariables();
		} else {
			RelevantVariables rvar = new RelevantVariables(rv);
			relevantVarsToUseForFPBP = rvar.getRelevantVariables();
		}
		
		
		if (m_ComputeInterpolantsFp) {
			s_Logger.debug("Computing forward relevant predicates...");
			computeForwardRelevantPredicates(relevantVarsToUseForFPBP, rv, trace, tracePrecondition);
			s_Logger.debug("Checking inductivity of forward relevant predicates...");
			assert checkPredicatesCorrect(m_InterpolantsFp, trace, tracePrecondition,
					tracePostcondition, "FP") : "invalid Hoare triple in FP";
		}
		
		if (m_LogInformation) {
			s_Logger.debug("Length of trace:" + trace.length());
//			new DebugMessage("#quantifiedPredicates in SP: {0}", m_NumberOfQuantifiedPredicates[0]);
			s_Logger.debug("#quantifiedPredicates in SP: " + m_NumberOfQuantifiedPredicates[0]);
			s_Logger.debug("#quantifiedPredicates in FP: " + m_NumberOfQuantifiedPredicates[1]);
		}
		
		if (m_ComputeInterpolantsSp && !m_ComputeInterpolantsFp) {
			m_InterpolantsSp = new IPredicate[trace.length()-1];

			s_Logger.debug("Computing strongest postcondition for given trace ...");
			if (trace.length() > 1) {
				for (int i=0; i<m_InterpolantsSp.length; i++) {
					if (trace.getSymbol(i) instanceof Call) {
						IPredicate p = m_SmtManager.strongestPostcondition(
								getForwardPredicateAtPosition(i-1, tracePrecondition, false),
								rv.getLocalVarAssignment(i),
								rv.getGlobalVarAssignment(i),
								rv.getOldVarAssignment(i),
								((NestedWord<CodeBlock>) trace).isPendingCall(i));
							m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
									p.getProcedures());
					} else if (trace.getSymbol(i) instanceof Return) {
							int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
							assert call_pos >= 0 && call_pos <= i : "Bad call position!";
							IPredicate callerPred = tracePrecondition;
							if (call_pos > 0) {
								callerPred = m_InterpolantsSp[call_pos - 1];
							}
							IPredicate p = m_SmtManager.strongestPostcondition(
									getForwardPredicateAtPosition(i-1, tracePrecondition, false), 
									callerPred,
									rv.getFormulaFromNonCallPos(i),
									rv.getLocalVarAssignment(call_pos),
									rv.getGlobalVarAssignment(call_pos)
									);
							m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
									p.getProcedures());

					} else {
							IPredicate p = m_SmtManager.strongestPostcondition(
									getForwardPredicateAtPosition(i-1, tracePrecondition, false),
									rv.getFormulaFromNonCallPos(i));
							m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
									p.getProcedures());
					}
				}
			}
			s_Logger.debug("Checking strongest postcondition...");
			assert checkPredicatesCorrect(m_InterpolantsSp, trace, tracePrecondition, 
					tracePostcondition, "SP with unsat core") : "invalid Hoare triple in SP with unsat core";
			
		}
		if (m_ComputeInterpolantsBp) {
			s_Logger.debug("Computing backward relevant predicates...");
			computeBackwardRelevantPredicates(relevantVarsToUseForFPBP, rv, trace, tracePostcondition);
			s_Logger.debug("Checking inductivity of backward relevant predicates...");
			assert checkInterpolantsCorrectBackwards(m_InterpolantsBp, trace, tracePrecondition,
					tracePostcondition, "BP") : "invalid Hoare triple in BP";
		}
		
		if (m_LogInformation) {
			s_Logger.debug("Length of trace:" + trace.length());
			s_Logger.debug("#quantifiedPredicates in WP: " + m_NumberOfQuantifiedPredicates[2]);
			s_Logger.debug("#quantifiedPredicates in BP: " + m_NumberOfQuantifiedPredicates[3]);
		}
		
		if (m_ComputeInterpolantsWp && !m_ComputeInterpolantsBp) {
			m_InterpolantsWp = new IPredicate[trace.length()-1];
			// Contains the predicates, which are computed during a Return with the second method, where the callerPred
			// is computed as wp(returnerPred, summaryOfCalledProcedure).
			Map<Integer, IPredicate> callerPredicatesComputed = new HashMap<Integer, IPredicate>();
			s_Logger.debug("Computing weakest precondition for given trace ...");
			if (trace.length() > 1) {
				for (int i = m_InterpolantsWp.length - 1; i >= 0; i--) {
					if (trace.getSymbol(i+1) instanceof Call) {
						if (callerPredicatesComputed.containsKey(i+1)) {
							
							IPredicate p = m_SmtManager.renameVarsOfOtherProcsToFreshVars(callerPredicatesComputed.get(i+1),
									((Call) trace.getSymbol(i+1)).getPreceedingProcedure());
							m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
									p.getVars(), p.getProcedures());
						} else {
							//((Call) trace.getSymbol(i+1)).getCallStatement().getMethodName()
							IPredicate p = m_SmtManager.weakestPrecondition(
									getBackwardPredicateAtPosition(i+1, tracePostcondition, false), 
									rv.getLocalVarAssignment(i+1),
									rv.getGlobalVarAssignment(i+1),
									rv.getOldVarAssignment(i+1),
									true);
							m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
									p.getVars(), p.getProcedures());
							
						}
					} else if (trace.getSymbol(i+1) instanceof Return) {
						int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i+1);
						TransFormula callTF = rv.getLocalVarAssignment(call_pos);
						TransFormula globalVarsAssignments = rv.getGlobalVarAssignment(call_pos);
						
						TransFormula summary = computeSummaryForInterproceduralTrace(trace, rv, 0, call_pos);
						IPredicate callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
						// If callerPred contains quantifier, compute it via the 2nd method
						if (callerPred instanceof BasicPredicateExplicitQuantifier) {
							summary = computeProcedureSummary(trace.getSubWord(call_pos, i), callTF,
									rv.getFormulaFromNonCallPos(i+1), 
									globalVarsAssignments,
									rv, call_pos);
							callerPred = m_SmtManager.weakestPrecondition(
									getBackwardPredicateAtPosition(i+1, tracePostcondition, false), 
									summary);
						}
						callerPredicatesComputed.put(call_pos, callerPred);
						IPredicate p = m_SmtManager.weakestPrecondition(
								getBackwardPredicateAtPosition(i+1, tracePostcondition, false), 
								callerPred, 
								rv.getFormulaFromNonCallPos(i+1), callTF, 
								globalVarsAssignments,
								m_ModifiedGlobals.getModifiedBoogieVars(((Return)trace.getSymbol(i+1)).getCorrespondingCall().getCallStatement().getMethodName())); 
						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
								p.getVars(), p.getProcedures());
					} else {
						IPredicate p = m_SmtManager.weakestPrecondition(
								getBackwardPredicateAtPosition(i+1, tracePostcondition, false),
								rv.getFormulaFromNonCallPos(i+1));
						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
								p.getVars(), p.getProcedures());
					}
				}
				
			}
		
			s_Logger.debug("Checking weakest precondition...");
//			assert checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition,
//					tracePostcondition, "WP with unsat core") : "invalid Hoare triple in WP with unsat core";
			assert checkInterpolantsCorrectBackwards(m_InterpolantsWp, trace, tracePrecondition,
					tracePostcondition, "WP with unsat core") : "invalid Hoare triple in WP with unsat core";
		}
		if (m_ComputeInterpolantsSp && m_ComputeInterpolantsWp) {
			checkSPImpliesWP(m_InterpolantsSp, m_InterpolantsWp);
		}
		if (m_ComputeInterpolantsFp && m_ComputeInterpolantsBp) {
			selectListOFPredicatesFromBothTypes();
		} else if (m_ComputeInterpolantsFp) {
			m_Interpolants = m_InterpolantsFp;
		} else if (m_ComputeInterpolantsSp) {
			m_Interpolants = m_InterpolantsSp;
		} else if (m_ComputeInterpolantsBp) {
			m_Interpolants = m_InterpolantsBp;
		} else {
			assert m_InterpolantsWp != null;
			m_Interpolants = m_InterpolantsWp;
		}
	}
	
	/***
	 * Selects a list of predicates from the predicates computed via strongest post-condition and the weakest precondition, such that the number
	 * of predicates containing quantifiers is minimized and a mix-up of the two types is avoided. (If the predicates are mixed-up, they may get
	 * non-inductive.)
	 * Predicates are selected in the following way: (TODO:)
	 * 
	 */
	private void selectListOFPredicatesFromBothTypes() {
		assert m_InterpolantsFp.length == m_InterpolantsBp.length;
		m_Interpolants = new IPredicate[m_InterpolantsBp.length];
		int i = 0; // position of predicate computed by strongest post-condition
		int j = m_InterpolantsBp.length; // position of predicate computed by weakest precondition
		while (i != j) {
			if (!(m_InterpolantsBp[j-1] instanceof BasicPredicateExplicitQuantifier)) {
				m_Interpolants[j-1] = m_InterpolantsBp[j-1];
				j--;
			} else if (!(m_InterpolantsFp[i] instanceof BasicPredicateExplicitQuantifier)) {
				m_Interpolants[i] = m_InterpolantsFp[i];
				i++;
			} else {
				int numOfQuantifiedVarsInFp = ((BasicPredicateExplicitQuantifier) m_InterpolantsFp[i]).getQuantifiedVariables().size();
				int numOfQuantifiedVarsInBp = ((BasicPredicateExplicitQuantifier) m_InterpolantsBp[j-1]).getQuantifiedVariables().size();
				if (numOfQuantifiedVarsInFp < numOfQuantifiedVarsInBp) {
					m_Interpolants[i] = m_InterpolantsFp[i];
					i++;
				} else {
					m_Interpolants[j-1] = m_InterpolantsBp[j-1];
					j--;
				}
			}
		}
	}
	
	
	
	/**
	 * Checks whether the trace consisting of only relevant statements
	 * is still infeasible. This check is desired, when we use unsatisfiable 
	 * cores of finer granularity. 
	 */
	private boolean stillInfeasible(RelevantTransFormulas rv) {
		TraceChecker tc = new TraceChecker(rv.getPrecondition(), 
				rv.getPostcondition(), null, rv.getTrace(), m_SmtManager, m_ModifiedGlobals);
		tc.unlockSmtManager();
		boolean result = (tc.isCorrect() == LBool.UNSAT);
		return result;
	}
	
	
	/**
	 * Select the statements from the given trace, which are contained in the unsatisfiable core. These statements contribute to the unsatisfiability
	 * of the trace, and therefore only these are important for the computations done afterwards.
	 */
	private Set<CodeBlock> filterOutIrrelevantStatements(NestedWord<CodeBlock> trace, Set<Term> unsat_coresAsSet,
			boolean[] localVarAssignmentAtCallInUnsatCore,
			boolean[] oldVarAssignmentAtCallInUnsatCore ) {
		Set<CodeBlock> codeBlocksInUnsatCore = new HashSet<CodeBlock>();
		for (int i = 0; i < trace.length(); i++) {
			if (!trace.isCallPosition(i) && unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getFormulaFromNonCallPos(i))) {
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			} else if (trace.isCallPosition(i) && 
					(unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getGlobalVarAssignment(i))
							|| unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getOldVarAssignment(i)))) {
				// The upper condition checks, whether the globalVarAssignments
				// is in unsat core, now check whether the local variable assignments
				// is in unsat core, if it is Call statement
				if (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getLocalVarAssignment(i))) {
					localVarAssignmentAtCallInUnsatCore[i] = true;
				}
				if (unsat_coresAsSet.contains(m_AAA.getAnnotatedSsa().getOldVarAssignment(i))) {
					oldVarAssignmentAtCallInUnsatCore[i] = true;
				}
				// Add the globalVarAssignments to the unsat_core, if it is a Call statement, otherwise it adds
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

	/**
	 * Compute forward relevant predicates for each position directly after the strongest post-condition has been
	 * computed. Formally, we have
	 * FP[i] = EXISTS irrelevantVars[i]. strongest-post(FP[i-1], relevantTransformulas[i]) 
	 */
	private void computeForwardRelevantPredicates(Set<BoogieVar>[] relevantVars, RelevantTransFormulas rv,
			NestedWord<CodeBlock> trace,
			IPredicate tracePrecondition) {
		m_InterpolantsSp = new IPredicate[trace.length() - 1];
		m_InterpolantsFp = new IPredicate[m_InterpolantsSp.length];
		
		if (trace.length() > 1) {
			for (int i=0; i<m_InterpolantsSp.length; i++) {
				IPredicate sp = null;
				if (trace.getSymbol(i) instanceof Call) {
					 sp = m_SmtManager.strongestPostcondition(
							getForwardPredicateAtPosition(i-1, tracePrecondition, true),
							rv.getLocalVarAssignment(i),
							rv.getGlobalVarAssignment(i),
							rv.getOldVarAssignment(i),
							((NestedWord<CodeBlock>) trace).isPendingCall(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(sp.getFormula(), sp.getVars(),
								sp.getProcedures());
				} else if (trace.getSymbol(i) instanceof Return) {
						int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
						assert call_pos >= 0 && call_pos <= i : "Bad call position!";
						IPredicate callerPred = tracePrecondition;
						if (call_pos > 0) {
							callerPred = m_InterpolantsFp[call_pos - 1];
						}
						sp = m_SmtManager.strongestPostcondition(
								getForwardPredicateAtPosition(i-1, tracePrecondition, true), 
								callerPred,
								rv.getFormulaFromNonCallPos(i),
								rv.getLocalVarAssignment(call_pos),
								rv.getGlobalVarAssignment(call_pos)
								);
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(sp.getFormula(), sp.getVars(),
								sp.getProcedures());

				} else {
						sp = m_SmtManager.strongestPostcondition(
								getForwardPredicateAtPosition(i-1, tracePrecondition, true),
								rv.getFormulaFromNonCallPos(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(sp.getFormula(), sp.getVars(),
								sp.getProcedures());
				}
				IPredicate fp = m_SmtManager.computeForwardRelevantPredicate(
						getForwardPredicateAtPosition(i, tracePrecondition, false), relevantVars[i+1]);
				m_InterpolantsFp[i] = m_PredicateUnifier.getOrConstructPredicate(fp.getFormula(), fp.getVars(), fp.getProcedures());
				if (m_CollectInformationAboutQuantifiedPredicates) {
					if (sp != null && sp instanceof BasicPredicateExplicitQuantifier) {
						m_NumberOfQuantifiedPredicates[0]++;
					}
					if (fp instanceof BasicPredicateExplicitQuantifier) {
						m_NumberOfQuantifiedPredicates[1]++;
					}
				}
			}
		}
		if (m_CollectInformationAboutSizeOfPredicates) {
			m_SizeOfPredicatesFP = computeSizeOfPredicates(m_InterpolantsFp);
		}
	}
	
	/**
	 * Compute backward relevant predicates for each position directly after the weakest precondition has been
	 * computed. Formally, we have
	 * BP[i] = FORALL irrelevantVars[i]. weakest-precondition(BP[i+1], relevantTransformulas[i]) 
	 */
	private void computeBackwardRelevantPredicates(Set<BoogieVar>[] relevantVars, RelevantTransFormulas rv,
			NestedWord<CodeBlock> trace,
			IPredicate tracePostcondition) {
		m_InterpolantsWp = new IPredicate[trace.length() - 1];
		m_InterpolantsBp = new IPredicate[m_InterpolantsWp.length];
		
		if (trace.length() > 1) {
			// Contains the predicates, which are computed during a Return with the second method, where the callerPred
			// is computed as wp(returnerPred, summaryOfCalledProcedure).
			Map<Integer, IPredicate> callerPredicatesComputed = new HashMap<Integer, IPredicate>();
			for (int i = m_InterpolantsWp.length - 1; i >= 0; i--) {
				IPredicate wp = null;
				if (trace.getSymbol(i+1) instanceof Call) {
					if (callerPredicatesComputed.containsKey(i+1)) {
						wp = m_SmtManager.renameVarsOfOtherProcsToFreshVars(callerPredicatesComputed.get(i+1),
								((Call) trace.getSymbol(i+1)).getPreceedingProcedure());
						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(wp.getFormula(),
								wp.getVars(),wp.getProcedures());
					} else {
						wp = m_SmtManager.weakestPrecondition(
								getBackwardPredicateAtPosition(i+1, tracePostcondition, true), 
								rv.getLocalVarAssignment(i+1),
								rv.getGlobalVarAssignment(i+1),
								rv.getOldVarAssignment(i+1),
								true);
						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(wp.getFormula(),
								wp.getVars(),wp.getProcedures());
						
					}
				} else if (trace.getSymbol(i+1) instanceof Return) {
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i+1);
					TransFormula callTF = rv.getLocalVarAssignment(call_pos);
					TransFormula globalVarsAssignments = rv.getGlobalVarAssignment(call_pos);
					// 1st method of computing the predicate right before of the corresponding Call-statement.
					// 1.1: Compute a summary of the statements from the beginning of the trace up to the Call-Statement, without including it.
					// 1.2: Compute the caller predicate as the strongest post-condition of the precondition and the summary.
					TransFormula summary = computeSummaryForInterproceduralTrace(trace, rv, 0, call_pos);
					IPredicate callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
					// If callerPred contains quantifiers, compute it via the 2nd method
					if (callerPred instanceof BasicPredicateExplicitQuantifier) {
						// 2nd method of computing the predicate right before of the corresponding Call-statement.
						// 2.1: Compute a summary of the statements from the beginning of the trace up to the Call-Statement, without including it.
						// 2.2: Compute the caller predicate as the strongest post-condition of the precondition and the summary.
						summary = computeProcedureSummary(trace.getSubWord(call_pos, i), callTF,
								rv.getFormulaFromNonCallPos(i+1), 
								globalVarsAssignments,
								rv, call_pos);
						callerPred = m_SmtManager.weakestPrecondition(
								getBackwardPredicateAtPosition(i+1, tracePostcondition, true), 
								summary);
					}
					callerPredicatesComputed.put(call_pos, callerPred);
					wp = m_SmtManager.weakestPrecondition(
							getBackwardPredicateAtPosition(i+1, tracePostcondition, true), 
							callerPred, 
							rv.getFormulaFromNonCallPos(i+1), callTF, 
							globalVarsAssignments,
							m_ModifiedGlobals.getModifiedBoogieVars(((Return)trace.getSymbol(i+1)).getCorrespondingCall().getCallStatement().getMethodName())); 
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(wp.getFormula(),
								wp.getVars(),wp.getProcedures());
				} else {
					wp = m_SmtManager.weakestPrecondition(
							getBackwardPredicateAtPosition(i+1, tracePostcondition, true),
							rv.getFormulaFromNonCallPos(i+1));
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(wp.getFormula(),
								wp.getVars(),wp.getProcedures());
				}
				IPredicate bp = m_SmtManager.computeBackwardRelevantPredicate(getBackwardPredicateAtPosition(i, tracePostcondition, false),
						relevantVars[i+1]);
				m_InterpolantsBp[i]  = m_PredicateUnifier.getOrConstructPredicate(bp.getFormula(),
						bp.getVars(), bp.getProcedures());
				if (m_CollectInformationAboutQuantifiedPredicates) {
					if (wp != null && wp instanceof BasicPredicateExplicitQuantifier) {
						m_NumberOfQuantifiedPredicates[2]++;
					}
					if (bp instanceof BasicPredicateExplicitQuantifier) {
						m_NumberOfQuantifiedPredicates[3]++;
					}
				}
			}
		}
		if (m_CollectInformationAboutSizeOfPredicates) {
			m_SizeOfPredicatesBP = computeSizeOfPredicates(m_InterpolantsBp);
		}
	}
	
	
	/***
	 *  Check for each predicate computed via the strongest post-condition, whether it implies the predicate computed via weakest precondition.
	 *  This check is desired, when predicates are computed twice (once via strongest post, and once via weakest pre-condition). 
	 *  It ensures the correctness of the predicates.
	 */
	private void checkSPImpliesWP(IPredicate[] interpolantsSP, IPredicate[] interpolantsWP) {
		s_Logger.debug("Checking implication of SP and WP...");
		for (int i = 0; i < interpolantsSP.length; i++) {
			LBool result = m_SmtManager.isCovered(interpolantsSP[i], interpolantsWP[i]);
			s_Logger.debug("SP {" + interpolantsSP[i] + "} ==> WP {" + interpolantsWP[i] + "} is " + 
						(result == LBool.UNSAT ? "valid" :
						(result == LBool.SAT ? "not valid" : result)));
			assert(result == LBool.UNSAT || result == LBool.UNKNOWN) : "checkSPImpliesWP failed";	
		}
	}
	
	
 	@Deprecated
	private void computeInterpolantsWithoutUsageOfUnsatCore(Set<Integer> interpolatedPositions) {
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		m_PredicateUnifier.declarePredicate(tracePrecondition);
		m_PredicateUnifier.declarePredicate(tracePostcondition);
		
		Word<CodeBlock> trace = m_Trace;
		
		unlockSmtManager();
		
		if (m_ComputeInterpolantsSp) {
			m_InterpolantsSp = new IPredicate[trace.length()-1];
			if (trace.length() == 1) {
				m_Interpolants = m_InterpolantsSp;
				return;
			}
			s_Logger.debug("Computing strongest postcondition for given trace ...");

			if (trace.getSymbol(0) instanceof Call) {
				IPredicate p = m_SmtManager.strongestPostcondition(
						tracePrecondition, (Call) trace.getSymbol(0),
						((NestedWord<CodeBlock>) trace).isPendingCall(0));
				m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
						p.getProcedures());
			} else {
				IPredicate p = m_SmtManager.strongestPostcondition(
						tracePrecondition, trace.getSymbol(0));
				m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
						p.getProcedures());
			}
			for (int i=1; i<m_InterpolantsSp.length; i++) {
				if (trace.getSymbol(i) instanceof Call) {
//					if (trace.length() == 19) {
//						int test = 0;
//					}
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1], (Call) trace.getSymbol(i),
							((NestedWord<CodeBlock>) trace).isPendingCall(i));
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				} else if (trace.getSymbol(i) instanceof Return) {
//					if (trace.length() == 19 && i >= 3) {
//						int test = 0;
//					}
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
					assert call_pos >= 0 && call_pos <= i : "Bad call position!";
					IPredicate callerPred = tracePrecondition;
					if (call_pos > 0) {
						callerPred = m_InterpolantsSp[call_pos - 1];
					}
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1], callerPred, (Return) trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
					
				
				} else {
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1],trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				}
			}
			s_Logger.debug("Checking strongest postcondition...");
			assert checkPredicatesCorrect(m_InterpolantsSp, trace, tracePrecondition, 
					tracePostcondition, "sp without unsat core") : "invalid Hoare triple in sp without unsat core";
		}

		if (m_ComputeInterpolantsWp) {
			m_InterpolantsWp = new IPredicate[trace.length()-1];
//			if (trace.length() == 1) {
//				m_Interpolants = m_InterpolantsWp;
//				return;
//			}
//			s_Logger.debug("Computing weakest precondition for given trace ...");
//			if (trace.getSymbol(m_InterpolantsWp.length) instanceof Call) {
//				// If the trace contains a Call statement, then it must be a NestedWord
//				NestedWord<CodeBlock> traceAsNW = ((NestedWord<CodeBlock>) trace);
//				int retPos = traceAsNW.getReturnPosition(m_InterpolantsWp.length);
//				IPredicate returnerPred = tracePostcondition;
//				if (retPos < m_InterpolantsWp.length) {
//					returnerPred = m_InterpolantsWp[retPos];
//				}
//				IPredicate p = m_SmtManager.weakestPrecondition(
//						tracePostcondition, returnerPred,
//						(Call) trace.getSymbol(m_InterpolantsWp.length),
//						(Return) trace.getSymbol(retPos) ,
//						traceAsNW.isPendingCall(m_InterpolantsWp.length));
//				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//						p.getVars(), p.getProcedures());
//			} else if (trace.getSymbol(m_InterpolantsWp.length) instanceof Return) {
//				int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(m_InterpolantsWp.length);
//				TransFormula summary = computeSummaryForTrace(getSubTrace(0, call_pos, trace));
//				IPredicate callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
//				// If the sub-trace between call_pos and returnPos (here: i) is shorter, than compute the
//				// callerPred in this way.
//				TransFormula callTF = ((Return) trace.getSymbol(m_InterpolantsWp.length)).getCorrespondingCall().getTransitionFormula();
//				TransFormula globalVarsAssignments = m_ModifiedGlobals.getGlobalVarsAssignment(((Return) trace.getSymbol(m_InterpolantsWp.length)).getCorrespondingCall().getCallStatement().getMethodName());
//				if ((m_InterpolantsWp.length - call_pos) < call_pos) {
//					summary = computeSummaryForTrace(getSubTrace(call_pos, m_InterpolantsWp.length - 1, trace), callTF,
//							trace.getSymbol(m_InterpolantsWp.length).getTransitionFormula(), globalVarsAssignments);
//					callerPred = m_SmtManager.weakestPrecondition(m_Postcondition, summary);
//				}
//				IPredicate p = m_SmtManager.weakestPrecondition(tracePostcondition,
//						callerPred, trace.getSymbol(m_InterpolantsWp.length).getTransitionFormula(),
//						callTF, globalVarsAssignments);
//				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//						p.getVars(), p.getProcedures());
//			} else {
//				IPredicate p = m_SmtManager.weakestPrecondition(
//						tracePostcondition, trace.getSymbol(m_InterpolantsWp.length));
//				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//						p.getVars(), p.getProcedures());
//			}
//
//			for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
//				if (trace.getSymbol(i+1) instanceof Call) {
//					NestedWord<CodeBlock> traceAsNW = (NestedWord<CodeBlock>) trace;					
//					int retPos = traceAsNW.getReturnPosition(i+1);
//					IPredicate returnerPred = tracePostcondition;
//					if (retPos < m_InterpolantsWp.length) {
//						returnerPred = m_InterpolantsWp[retPos];
//					}
//					IPredicate p = m_SmtManager.weakestPrecondition(
//							m_InterpolantsWp[i+1], returnerPred, 
//							(Call) trace.getSymbol(i+1),
//							(Return) trace.getSymbol(retPos),
//							traceAsNW.isPendingCall(i+1));
//					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//							p.getVars(), p.getProcedures());
//				} else if (trace.getSymbol(i+1) instanceof Return) {
//					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i+1);
//					TransFormula summary = computeSummaryForTrace(getSubTrace(0, call_pos, trace));
//					IPredicate callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
//					// If the sub-trace between call_pos and returnPos (here: i) is shorter, than compute the
//					// callerPred in this way.
//					TransFormula callTF = ((Return) trace.getSymbol(i)).getCorrespondingCall().getTransitionFormula();
//					TransFormula globalVarsAssignments = m_ModifiedGlobals.getGlobalVarsAssignment(((Return) trace.getSymbol(i)).getCorrespondingCall().getCallStatement().getMethodName());
//					if ((i - call_pos) < call_pos) {
//						summary = computeSummaryForTrace(getSubTrace(call_pos, i - 1, trace), callTF,
//								trace.getSymbol(i).getTransitionFormula(), globalVarsAssignments);
//						callerPred = m_SmtManager.weakestPrecondition(m_InterpolantsWp[i+1], 
//								summary);;
//					}
//					
//					IPredicate p = m_SmtManager.weakestPrecondition(
//							m_InterpolantsWp[i+1], callerPred, trace.getSymbol(i+1).getTransitionFormula(), callTF, globalVarsAssignments); 
//					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//							p.getVars(), p.getProcedures());
//				} else {
//					IPredicate p = m_SmtManager.weakestPrecondition(
//							m_InterpolantsWp[i+1], trace.getSymbol(i+1));
//					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
//							p.getVars(), p.getProcedures());
//				}
//			}
			s_Logger.debug("Checking weakest precondition...");
			assert checkPredicatesCorrect(m_InterpolantsWp, trace, tracePrecondition, 
					tracePostcondition, "wp without unsat core") : "invalid Hoare triple in wp without unsat core";
		}
		if (m_ComputeInterpolantsSp) {
			m_Interpolants = m_InterpolantsSp;
		} else {
			assert (m_ComputeInterpolantsWp);
			m_Interpolants = m_InterpolantsWp;
		}
	}
 	
 	/***
 	 * Checks whether the given predicates are inductive (correct).
 	 * For each statement st_i from the given trace, it checks whether {predicates[i-1]} st_i {predicates[i]} is a Hoare triple.
 	 */
	boolean checkPredicatesCorrect(IPredicate[] predicates,
								  Word<CodeBlock> trace, 
								  IPredicate tracePrecondition, 
								  IPredicate tracePostcondition,
								  String computation) {
		LBool result;
		for (int i=-1; i< predicates.length; i++) {
			 result = isHoareTriple(i+1, tracePrecondition, tracePostcondition, 
						predicates, trace);
			 if (result == LBool.SAT) {
				 s_Logger.debug("Trace length: " + trace.length());
				 s_Logger.debug("Stmt: " + (i+1));
				 return false;
			 }
			 assert result == LBool.UNSAT || result == LBool.UNKNOWN : 
				 "invalid Hoare triple in " + computation;
		}
		return true;
	}
	
	/***
	 * Checks whether the given predicates are inductive (correct).
 	 * For each statement st_i from the given trace, it checks whether {predicates[i-1]} st_i {predicates[i]} is a Hoare triple, but it starts
 	 * at the end of the list of predicates and proceeds backwards.
 	 * This ensures, that we get the first statement st, such that the corresponding Hoare triple is wrong.
 	 * @see checkPredicatesCorrect
 	 */
	boolean checkInterpolantsCorrectBackwards(IPredicate[] interpolants,
			Word<CodeBlock> trace, 
			IPredicate tracePrecondition, 
			IPredicate tracePostcondition,
			String computation) {
		LBool result;
		for (int i=interpolants.length - 1; i >= 0; i--) {
			result = isHoareTriple(i+1, tracePrecondition, tracePostcondition, 
					interpolants, trace);
			if (result == LBool.SAT) {
				s_Logger.debug("Trace length: " + trace.length());
				s_Logger.debug("Stmt: " + (i+1));
				return false;
			}
			assert result == LBool.UNSAT || result == LBool.UNKNOWN : 
				"invalid Hoare triple in " + computation;
		}
		return true;
	}
	
	private IPredicate getInterpolantAtPosition(int i, IPredicate tracePrecondition,
			IPredicate tracePostcondition, IPredicate[] interpolants) {
		assert (i>= -1 && i<= interpolants.length);
		if (i == -1) {
			return tracePrecondition;
		} else if (i == interpolants.length) {
			return tracePostcondition;
		} else {
			return interpolants[i];
		}
	}
	
	/***
 	 * Checks for a given statement st, a predicate %PHI and a predicate %PSI, whether the Hoare triple
 	 * {%PHI} st {%PSI} is correct.
 	 */
	private LBool isHoareTriple(int i, IPredicate tracePrecondition, 
			IPredicate tracePostcondition, 
			IPredicate[] interpolants, Word<CodeBlock> trace) {
		IPredicate pre = getInterpolantAtPosition(i-1, tracePrecondition, 
				tracePostcondition, interpolants);
		IPredicate post = getInterpolantAtPosition(i, tracePrecondition, 
				tracePostcondition, interpolants);
		CodeBlock cb = trace.getSymbol(i);
		EdgeChecker ec = new EdgeChecker(m_SmtManager, m_ModifiedGlobals);
		ec.assertCodeBlock(cb);
		ec.assertPrecondition(pre);
		LBool result;
		if (cb instanceof Call) {
			result = ec.postCallImplies(post);
		} else if (cb instanceof Return) {
			NestedWord<CodeBlock> nw = (NestedWord<CodeBlock>) trace;
			assert nw.isReturnPosition(i);
			int callPosition = nw.getCallPosition(i); 
			IPredicate callPredecessor = getInterpolantAtPosition(callPosition-1, 
					tracePrecondition, tracePostcondition, interpolants);
			ec.assertHierPred(callPredecessor);
			result = ec.postReturnImplies(post);
			ec.unAssertHierPred();
		} else if (cb instanceof InterproceduralSequentialComposition) {
			result = ec.postInternalImplies(post); 
		} else {
			assert (cb instanceof SequentialComposition) || 
				(cb instanceof ParallelComposition) || 
				(cb instanceof StatementSequence) ||
				(cb instanceof Summary);
			result = ec.postInternalImplies(post); 
		}
		ec.unAssertPrecondition();
		ec.unAssertCodeBlock();
		s_Logger.debug("Hoare triple {" + pre + "}, " + cb + " {" 
											+ post + "} is " + (result == LBool.UNSAT ? "valid" :
												(result == LBool.SAT ? "not valid" : result)));
		return result;
	}
	
	
	@Override
	protected AnnotateAndAsserter getAnnotateAndAsserter(NestedFormulas<Term, Term> ssa) {
		if (m_useUnsatCoreOfFineGranularity) {
			return new AnnotateAndAsserterConjuncts(m_SmtManager, ssa, m_DefaultTransFormulas); 
		} else {
			return new AnnotateAndAsserter(m_SmtManager, ssa);
		}
	}
	
	/***
 	 * Returns the size of predicates (either forward predicates or backward predicates depending on the parameter interpolation).
 	 */
	@Override
	public int[] getSizeOfPredicates(INTERPOLATION interpolation) {
		switch (interpolation) {
		case ForwardPredicates:
			return getSizeOfPredicatesFP();
		case BackwardPredicates:
			return getSizeOfPredicatesBP();
		default:
			return super.getSizeOfPredicates(interpolation);
		}
	}
	
	@Override
	public int getTotalNumberOfPredicates(INTERPOLATION interpolation) {
		switch (interpolation) {
		case ForwardPredicates:
			return m_InterpolantsFp != null ? m_InterpolantsFp.length : 0;
		case BackwardPredicates:
			return m_InterpolantsBp != null ? m_InterpolantsBp.length : 0;
		default:
			return super.getTotalNumberOfPredicates(interpolation);
		}
	}

	public static class TraceCheckerBenchmarkSpWp extends TraceCheckerBenchmark {

		@Override
		public TraceCheckerBenchmark copyAndAdd(
				TraceCheckerBenchmark traceCheckerBenchmark) {
			// TODO Auto-generated method stub
			return super.copyAndAdd(traceCheckerBenchmark);
		}
		
	}

}
