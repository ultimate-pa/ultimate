package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;

public class TraceCheckerSpWp extends TraceChecker {
	
	protected IPredicate[] m_InterpolantsSp;
	protected IPredicate[] m_InterpolantsWp;
	
	
	private static boolean m_useUnsatCore = true;
	private static boolean m_ComputeInterpolantsSp = !true;
	private static boolean m_ComputeInterpolantsWp = true;

	public TraceCheckerSpWp(IPredicate precondition, IPredicate postcondition,
			Word<CodeBlock> trace, SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			PrintWriter debugPW) {
		super(precondition, postcondition, trace, smtManager, modifiedGlobals, debugPW);
	}

	@Override
	public void computeInterpolants(Set<Integer> interpolatedPositions, 
			PredicateUnifier predicateUnifier) {
		m_PredicateUnifier = predicateUnifier;
		if (m_useUnsatCore) {
			computeInterpolantsWithUsageOfUnsatCore(interpolatedPositions);
		} else {
			computeInterpolantsWithoutUsageOfUnsatCore(interpolatedPositions);
		}
	}
	
	public IPredicate getInterpolanstsSPAtPosition(int i) {
		assert m_InterpolantsSp != null : "InterpolantsSP hasn't been computed, yet.";
		assert i >= 0 && i < m_InterpolantsSp.length : ("The given position "+ i
				+ " is not a correct position. #Interpolants = " 
				+ m_InterpolantsSp.length);
		return m_InterpolantsSp[i];
	}
	
	public IPredicate getInterpolanstsWPAtPosition(int i) {
		assert m_InterpolantsWp != null : "InterpolantsWP hasn't been computed, yet.";
		assert i >= 0 && i < m_InterpolantsWp.length : "The given position "+ i + " is not a correct position!";
		return m_InterpolantsWp[i];
	}
	
	
	/**
	 * Computes the sequential composition of the statements from the given trace.
	 * TODO: Currently, it only computes composition for statements without Calls (esp. PendingCalls) and Returns.
	 */
	private TransFormula computeSummaryForTrace(Word<CodeBlock> trace, RelevantTransFormulas rv) {
		TransFormula[] transFormulasToComputeSummaryFor = new TransFormula[trace.length()];
		for (int i = 0; i < trace.length(); i++) {
			transFormulasToComputeSummaryFor[i] = rv.getRelevantTransFormulaAtPosition(i);
		}
		return TransFormula.sequentialComposition(m_SmtManager.getBoogie2Smt(), true, transFormulasToComputeSummaryFor);
	}
	
	private TransFormula computeSummaryForTrace(Word<CodeBlock> trace, TransFormula Call, 
			TransFormula Return, 
			TransFormula oldVarsAssignment,
			RelevantTransFormulas rv) {
		TransFormula procedureSummary = computeSummaryForTrace(trace, rv);
		return TransFormula.sequentialCompositionWithCallAndReturn(m_SmtManager.getBoogie2Smt(), true, Call, oldVarsAssignment, procedureSummary, Return);
	}
	
	
	public static boolean interpolantsSPComputed() {
		return m_ComputeInterpolantsSp;
	}

	public static boolean interpolantsWPComputed() {
		return m_ComputeInterpolantsWp;
	}

	private void computeInterpolantsWithUsageOfUnsatCore(Set<Integer> interpolatedPositions) {
		
		Term[] unsat_core = m_SmtManager.getScript().getUnsatCore();
		
		Set<Term> unsat_coresAsSet = new HashSet<Term>(Arrays.asList(unsat_core));
		
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		m_PredicateUnifier.declarePredicate(tracePrecondition);
		m_PredicateUnifier.declarePredicate(tracePostcondition);
		Word<CodeBlock> trace = m_Trace;
		Set<CodeBlock> codeBlocksInUnsatCore = new HashSet<CodeBlock>();
		
		unlockSmtManager();
		
		boolean[] localVarAssignmentAtCallInUnsatCore = new boolean[trace.length()];
		// Filter out the statements, which doesn't occur in the unsat core.
		for (int i = 0; i < trace.length(); i++) {
			
			if (unsat_coresAsSet.contains(m_AnnotatedSsa.getFormulas()[i])) {
				// The upper condition checks, whether the globalVarAssignments
				// is in unsat core, now check whether the local variable assignments
				// is in unsat core, if it is Call statement
				if (trace.getSymbol(i) instanceof Call) {
					// Check whether the local variable assignments are also in unsat core.
					if (unsat_coresAsSet.contains(m_AnnotatedSsa.getLocalVarAssignmentAtCall().get(i))) {
						localVarAssignmentAtCallInUnsatCore[i] = true;
					}
				}
				// Add the globalVarAssignments to the unsat_core
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			} else {
				if (trace.getSymbol(i) instanceof Call) {
					if (unsat_coresAsSet.contains(m_AnnotatedSsa.getLocalVarAssignmentAtCall().get(i))) {
						localVarAssignmentAtCallInUnsatCore[i] = true;
					}
				}
			}
		}
		
		@SuppressWarnings("unchecked")
		RelevantTransFormulas rv = new RelevantTransFormulas(NestedWord.nestedWord(trace),
				codeBlocksInUnsatCore,
				m_ModifiedGlobals,
				localVarAssignmentAtCallInUnsatCore,
				m_SmtManager);
		
		if (m_ComputeInterpolantsSp) {
			m_InterpolantsSp = new IPredicate[trace.length()-1];

			s_Logger.debug("Computing strongest postcondition for given trace ...");
			
			if (trace.length() > 1) {
				if (trace.getSymbol(0) instanceof Call) {
					IPredicate p = m_SmtManager.strongestPostcondition(tracePrecondition,
							rv.getRelevantTransFormulaAtPosition(0),
							rv.getGlobalVarAssignmentAtCallPosition(0),
							((NestedWord<CodeBlock>) trace).isPendingCall(0));							
					m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				} else {
					IPredicate p = m_SmtManager.strongestPostcondition(tracePrecondition,
							rv.getRelevantTransFormulaAtPosition(0));
					m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				}
			}

			for (int i=1; i<m_InterpolantsSp.length; i++) {
				if (trace.getSymbol(i) instanceof Call) {
					IPredicate p = m_SmtManager.strongestPostcondition(m_InterpolantsSp[i-1],
							rv.getRelevantTransFormulaAtPosition(i),
							rv.getGlobalVarAssignmentAtCallPosition(i),
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
						IPredicate p = m_SmtManager.strongestPostcondition(m_InterpolantsSp[i-1], 
								callerPred,
								rv.getRelevantTransFormulaAtPosition(i),
								rv.getRelevantTransFormulaAtPosition(call_pos),
								rv.getGlobalVarAssignmentAtCallPosition(call_pos)
								);
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());

				} else {
						IPredicate p = m_SmtManager.strongestPostcondition(m_InterpolantsSp[i-1],
								rv.getRelevantTransFormulaAtPosition(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
				}
			}
			s_Logger.debug("Checking strongest postcondition...");
			checkInterpolantsCorrect(m_InterpolantsSp, trace, tracePrecondition, tracePostcondition);
		}
		if (m_ComputeInterpolantsWp) {
			m_InterpolantsWp = new IPredicate[trace.length()-1];
			// Contains the predicates, which are computed during a Return with the second method, where the callerPred
			// is computed as wp(returnerPred, summaryOfCalledProcedure).
			Map<Integer, IPredicate> callerPredicatesComputed = new HashMap<Integer, IPredicate>();
			s_Logger.debug("Computing weakest precondition for given trace ...");
			if (trace.length() > 1) {
				if (trace.getSymbol(m_InterpolantsWp.length) instanceof Call) {
					// If the trace contains a Call statement, then it must be a NestedWord
					NestedWord<CodeBlock> traceAsNW = ((NestedWord<CodeBlock>) trace);
					IPredicate p = m_SmtManager.weakestPrecondition(
							tracePostcondition, 
							rv.getRelevantTransFormulaAtPosition(m_InterpolantsWp.length),
							rv.getGlobalVarAssignmentAtCallPosition(m_InterpolantsWp.length),
							traceAsNW.isPendingCall(m_InterpolantsWp.length));
					m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());

				} else if (trace.getSymbol(m_InterpolantsWp.length) instanceof Return) {
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(m_InterpolantsWp.length);
					IPredicate callerPred = null;
					TransFormula callTF = rv.getRelevantTransFormulaAtPosition(call_pos);
					TransFormula globalVarsAssignments = rv.getGlobalVarAssignmentAtCallPosition(call_pos);
					if ((m_InterpolantsWp.length - call_pos) >= call_pos) {
						TransFormula summary = computeSummaryForTrace(getSubTrace(0, call_pos, trace), rv);
						callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
					} else {
					// If the sub-trace between call_pos and returnPos (here: i) is shorter, than compute the
					// callerPred in this way.
						TransFormula summary = computeSummaryForTrace(getSubTrace(call_pos, m_InterpolantsWp.length - 1, trace), callTF,
								rv.getRelevantTransFormulaAtPosition(m_InterpolantsWp.length), 
								globalVarsAssignments,
								rv);
						callerPred = m_SmtManager.weakestPrecondition(m_Postcondition, summary);
					}
					callerPredicatesComputed.put(call_pos, callerPred);
					IPredicate p = m_SmtManager.weakestPrecondition(tracePostcondition,
							callerPred, 
							rv.getRelevantTransFormulaAtPosition(m_InterpolantsWp.length),
							callTF, globalVarsAssignments);
					m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				}
				else {
					IPredicate p = m_SmtManager.weakestPrecondition(
							tracePostcondition, rv.getRelevantTransFormulaAtPosition(m_InterpolantsWp.length));
					m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				}
			}
			for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
				if (trace.getSymbol(i+1) instanceof Call) {
					if (callerPredicatesComputed.containsKey(i+1)) {
						IPredicate p = callerPredicatesComputed.get(i+1);
						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
								p.getVars(), p.getProcedures());
					} else {
						IPredicate p = m_SmtManager.weakestPrecondition(
								m_InterpolantsWp[i+1], 
								rv.getRelevantTransFormulaAtPosition(i+1),
								rv.getGlobalVarAssignmentAtCallPosition(i+1),
								true);
						m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
								p.getVars(), p.getProcedures());
						
					}
				} else if (trace.getSymbol(i+1) instanceof Return) {
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i+1);
					IPredicate callerPred = null;
					TransFormula callTF = rv.getRelevantTransFormulaAtPosition(call_pos);
					TransFormula globalVarsAssignments = rv.getGlobalVarAssignmentAtCallPosition(call_pos);
					
					if ((i - call_pos) >= call_pos) {
						TransFormula summary = computeSummaryForTrace(getSubTrace(0, call_pos, trace), rv);
						callerPred = m_SmtManager.strongestPostcondition(m_Precondition, summary);
					} else {
					// If the sub-trace between call_pos and returnPos (here: i) is shorter, then compute the
					// callerPred in this way.
						TransFormula summary = computeSummaryForTrace(getSubTrace(call_pos, i - 1, trace), callTF,
								rv.getRelevantTransFormulaAtPosition(i+1), 
								globalVarsAssignments,
								rv);
						callerPred = m_SmtManager.weakestPrecondition(m_InterpolantsWp[i+1], 
								summary);
					}
					callerPredicatesComputed.put(call_pos, callerPred);
					IPredicate p = m_SmtManager.weakestPrecondition(
							m_InterpolantsWp[i+1], 
							callerPred, 
							rv.getRelevantTransFormulaAtPosition(i+1), callTF, 
							globalVarsAssignments); 
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				} else {
					IPredicate p = m_SmtManager.weakestPrecondition(
							m_InterpolantsWp[i+1], rv.getRelevantTransFormulaAtPosition(i+1));
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				}
			}

			s_Logger.debug("Checking weakest precondition...");
			checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition, tracePostcondition);
		}
		if (m_ComputeInterpolantsSp) {
			m_Interpolants = m_InterpolantsSp;
		} else {
			assert m_InterpolantsWp != null;
			m_Interpolants = m_InterpolantsWp;
		}
	}
	
	/**
	 * Returns a sub-trace of the given trace, from startPos to endPos.
	 */
	private Word<CodeBlock> getSubTrace(int startPos, int endPos, Word<CodeBlock> trace) {
		CodeBlock[] codeBlocks = new CodeBlock[endPos - startPos];
		for (int i = startPos; i < endPos; i++) {
			codeBlocks[i - startPos] = trace.getSymbol(i);
		}
		return new Word<CodeBlock>(codeBlocks);
	}
	
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
			checkInterpolantsCorrect(m_InterpolantsSp, trace, tracePrecondition, tracePostcondition);
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
			checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition, tracePostcondition);
		}
		if (m_ComputeInterpolantsSp) {
			m_Interpolants = m_InterpolantsSp;
		} else {
			assert (m_ComputeInterpolantsWp);
			m_Interpolants = m_InterpolantsWp;
		}
	}

	void checkInterpolantsCorrect(IPredicate[] interpolants,
								  Word<CodeBlock> trace, 
								  IPredicate tracePrecondition, 
								  IPredicate tracePostcondition) {
		LBool result;
//		result = isHoareTriple(0, tracePrecondition, tracePostcondition, 
//				interpolants, trace);
//		assert result == LBool.UNSAT || result == LBool.UNKNOWN;
		for (int i=-1; i<interpolants.length; i++) {
			 result = isHoareTriple(i+1, tracePrecondition, tracePostcondition, 
						interpolants, trace);
			 if (result == LBool.SAT) {
				 s_Logger.debug("Trace length: " + trace.length());
				 s_Logger.debug("Stmt: " + i);
			 }
			 assert result == LBool.UNSAT || result == LBool.UNKNOWN;
		}
//		if (trace.length() > 1) {
//			result = isHoareTriple(interpolants.length, tracePrecondition, 
//					tracePostcondition,	interpolants, trace);
//			assert result == LBool.UNSAT || result == LBool.UNKNOWN;
//		}
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
			throw new UnsupportedOperationException("not yet inplemented");
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


}
