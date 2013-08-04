package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.InterproceduralSequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class TraceCheckerSpWp extends TraceChecker {
	
	protected IPredicate[] m_InterpolantsSp;
	protected IPredicate[] m_InterpolantsWp;
	
	//TODO: These two members are just for debugging purposes, they should removed
	// after the computation of SP and WP has been justified to be correct.
	protected IPredicate[] m_InterpolantsSpNotSimplified;
	protected IPredicate[] m_InterpolantsWpNotSimplified;
	
	private static boolean m_useUnsatCore = !true;
	private static boolean m_ComputeInterpolantsSp = true;
	private static boolean m_ComputeInterpolantsWp = !true;

	public TraceCheckerSpWp(SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			PrintWriter debugPW) {
		super(smtManager, modifiedGlobals, debugPW);
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
		// Filter out the statements, which doesn't occur in the unsat core.
		for (int i = 0; i < trace.length(); i++) {
			if (isInUnsatCore(i, unsat_coresAsSet)) {
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			}
		}

		
		if (m_ComputeInterpolantsSp) {
			m_InterpolantsSp = new IPredicate[trace.length()-1];
			IPredicate lastlyComputedPred = tracePrecondition;
			IPredicate predOfLastStmtInUnsatCore = tracePrecondition;

			s_Logger.debug("Computing strongest postcondition for given trace ...");

			for (int i=0; i<m_InterpolantsSp.length; i++) {
				if (trace.getSymbol(i) instanceof Call) {
					if (codeBlocksInUnsatCore.contains(trace.getSymbol(i))) {
						IPredicate p = m_SmtManager.strongestPostcondition(
								predOfLastStmtInUnsatCore, (Call) trace.getSymbol(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
						predOfLastStmtInUnsatCore = m_InterpolantsSp[i];
						lastlyComputedPred = m_InterpolantsSp[i];
					} else {
						IPredicate p = m_SmtManager.strongestPostconditionSpecial(
								lastlyComputedPred, trace.getSymbol(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
						lastlyComputedPred = m_InterpolantsSp[i];
					}
				} else if (trace.getSymbol(i) instanceof Return) {
					if (codeBlocksInUnsatCore.contains(trace.getSymbol(i))) {
						int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
						assert call_pos >= 0 && call_pos <= i : "Bad call position!";
						IPredicate callerPred = tracePrecondition;
						if (call_pos > 0) {
							callerPred = m_InterpolantsSp[call_pos - 1];
						}
						IPredicate p = m_SmtManager.strongestPostcondition(
								predOfLastStmtInUnsatCore, callerPred, (Return) trace.getSymbol(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
						predOfLastStmtInUnsatCore = m_InterpolantsSp[i];
						lastlyComputedPred = m_InterpolantsSp[i];
					} else {
						// TODO: Probably, we also have to define a special method for Return and Call statement.
						IPredicate p = m_SmtManager.strongestPostconditionSpecial(
								lastlyComputedPred, trace.getSymbol(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
						lastlyComputedPred = m_InterpolantsSp[i];
					}

				} else {
					if (codeBlocksInUnsatCore.contains(trace.getSymbol(i))) {
						IPredicate p = m_SmtManager.strongestPostcondition(
								predOfLastStmtInUnsatCore, trace.getSymbol(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
						predOfLastStmtInUnsatCore = m_InterpolantsSp[i];
						lastlyComputedPred = m_InterpolantsSp[i];
					} else {
						IPredicate p = m_SmtManager.strongestPostconditionSpecial(
								lastlyComputedPred, trace.getSymbol(i));
						m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
								p.getProcedures());
						lastlyComputedPred = m_InterpolantsSp[i];
					}
				}
			}
			s_Logger.debug("Checking strongest postcondition...");
			checkInterpolantsCorrect(m_InterpolantsSp, m_InterpolantsSpNotSimplified, trace, tracePrecondition, tracePostcondition);
		}
		if (m_ComputeInterpolantsWp) {
			m_InterpolantsWp = new IPredicate[trace.length()-1];
			IPredicate lastlyComputedPred = tracePostcondition;
			IPredicate predOfLastStmtInUnsatCore = tracePostcondition;

			s_Logger.debug("Computing weakest precondition for given trace ...");
			lastlyComputedPred = m_SmtManager.weakestPrecondition(
					tracePostcondition, trace.getSymbol(m_InterpolantsWp.length));
			m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(lastlyComputedPred.getFormula(),
					lastlyComputedPred.getVars(),
					lastlyComputedPred.getProcedures());

			for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
				m_InterpolantsWp[i] = m_SmtManager.weakestPrecondition(
						m_InterpolantsWp[i+1], trace.getSymbol(i+1));
			}

			s_Logger.debug("Checking weakest precondition...");
			checkInterpolantsCorrect(m_InterpolantsWp, m_InterpolantsWpNotSimplified,trace, tracePrecondition, tracePostcondition);
		}
		if (m_ComputeInterpolantsSp) {
			m_Interpolants = m_InterpolantsSp;
		} else {
			assert m_InterpolantsWp != null;
			m_Interpolants = m_InterpolantsWp;
		}
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
			m_InterpolantsSpNotSimplified = new IPredicate[trace.length()-1];
			s_Logger.debug("Computing strongest postcondition for given trace ...");

			if (trace.getSymbol(0) instanceof Call) {
				IPredicate p = m_SmtManager.strongestPostcondition(
						tracePrecondition, (Call) trace.getSymbol(0),
						((NestedWord<CodeBlock>) trace).isPendingCall(0));
				m_InterpolantsSpNotSimplified[0] = p;
				m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
						p.getProcedures());
			} else {
				IPredicate p = m_SmtManager.strongestPostcondition(
						tracePrecondition, trace.getSymbol(0));
				m_InterpolantsSpNotSimplified[0] = p;
				m_InterpolantsSp[0] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
						p.getProcedures());
			}
			for (int i=1; i<m_InterpolantsSp.length; i++) {
				if (trace.getSymbol(i) instanceof Call) {
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1], (Call) trace.getSymbol(i),
							((NestedWord<CodeBlock>) trace).isPendingCall(i));
					m_InterpolantsSpNotSimplified[i] = p;
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				} else if (trace.getSymbol(i) instanceof Return) {
					if (trace.length() == 5 && i >= 3) {
						int test = 0;
					}
					int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
					assert call_pos >= 0 && call_pos <= i : "Bad call position!";
					IPredicate callerPred = tracePrecondition;
					if (call_pos > 0) {
						callerPred = m_InterpolantsSp[call_pos - 1];
					}
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1], callerPred, (Return) trace.getSymbol(i));
					m_InterpolantsSpNotSimplified[i] = p;
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
					
				
				} else {
					IPredicate p = m_SmtManager.strongestPostcondition(
							m_InterpolantsSp[i-1],trace.getSymbol(i));
					m_InterpolantsSpNotSimplified[i] = p;
					m_InterpolantsSp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(), p.getVars(),
							p.getProcedures());
				}
			}
			s_Logger.debug("Checking strongest postcondition...");
			checkInterpolantsCorrect(m_InterpolantsSp, m_InterpolantsSpNotSimplified, trace, tracePrecondition, tracePostcondition);
		}

		if (m_ComputeInterpolantsWp) {
			m_InterpolantsWp = new IPredicate[trace.length()-1];
			s_Logger.debug("Computing weakest precondition for given trace ...");
			if (trace.getSymbol(m_InterpolantsWp.length) instanceof Call) {
				// If the trace contains a Call statement, then it must be a NestedWord
				NestedWord<CodeBlock> traceAsNW = ((NestedWord<CodeBlock>) trace);
				int retPos = traceAsNW.getReturnPosition(m_InterpolantsWp.length);
				IPredicate returnerPred = tracePostcondition;
				if (retPos < m_InterpolantsWp.length) {
					returnerPred = m_InterpolantsWp[retPos];
				}
				IPredicate p = m_SmtManager.weakestPrecondition(
						tracePostcondition, returnerPred,
						(Call) trace.getSymbol(m_InterpolantsWp.length),
						(Return) trace.getSymbol(retPos) ,
						traceAsNW.isPendingCall(m_InterpolantsWp.length));
				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
						p.getVars(), p.getProcedures());
			} else if (trace.getSymbol(m_InterpolantsWp.length) instanceof Return) {
				IPredicate p = m_SmtManager.weakestPrecondition(
						tracePostcondition, (Return) trace.getSymbol(m_InterpolantsWp.length));
				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
						p.getVars(), p.getProcedures());
			} else {
				IPredicate p = m_SmtManager.weakestPrecondition(
						tracePostcondition, trace.getSymbol(m_InterpolantsWp.length));
				m_InterpolantsWp[m_InterpolantsWp.length-1] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
						p.getVars(), p.getProcedures());
			}

			for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
				if (trace.getSymbol(i+1) instanceof Call) {
					NestedWord<CodeBlock> traceAsNW = (NestedWord<CodeBlock>) trace;					
					int retPos = traceAsNW.getReturnPosition(i+1);
					IPredicate returnerPred = tracePostcondition;
					if (retPos < m_InterpolantsWp.length) {
						returnerPred = m_InterpolantsWp[retPos];
					}
					IPredicate p = m_SmtManager.weakestPrecondition(
							m_InterpolantsWp[i+1], returnerPred, 
							(Call) trace.getSymbol(i+1),
							(Return) trace.getSymbol(retPos),
							traceAsNW.isPendingCall(i+1));
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				} else if (trace.getSymbol(i+1) instanceof Return) {
					IPredicate p = m_SmtManager.weakestPrecondition(
							m_InterpolantsWp[i+1], (Return) trace.getSymbol(i+1)); 
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				} else {
					IPredicate p = m_SmtManager.weakestPrecondition(
							m_InterpolantsWp[i+1], trace.getSymbol(i+1));
					m_InterpolantsWp[i] = m_PredicateUnifier.getOrConstructPredicate(p.getFormula(),
							p.getVars(), p.getProcedures());
				}
			}
			s_Logger.debug("Checking weakest precondition...");
			checkInterpolantsCorrect(m_InterpolantsWp, m_InterpolantsWpNotSimplified, trace, tracePrecondition, tracePostcondition);
		}
		if (m_ComputeInterpolantsSp) {
			m_Interpolants = m_InterpolantsSp;
		} else {
			assert (m_ComputeInterpolantsWp);
			m_Interpolants = m_InterpolantsWp;
		}
	}

	/**
	 * Checks whether the term at position pos is contained in unsat_core.
	 */
	private boolean isInUnsatCore(int pos, Set<Term> unsat_core) {
		Term annotTerm = m_AnnotatedSsa.getTerms()[pos];
		return unsat_core.contains(annotTerm);
	}
	
	void checkInterpolantsCorrect(IPredicate[] interpolants,IPredicate[] interpolantsNotSimplified,
								  Word<CodeBlock> trace, 
								  IPredicate tracePrecondition, 
								  IPredicate tracePostcondition) {
		LBool result;
		result = isHoareTriple(0, tracePrecondition, tracePostcondition, 
				interpolants, trace);
		assert result == LBool.UNSAT || result == LBool.UNKNOWN;
		for (int i=0; i<interpolants.length-1; i++) {
			 result = isHoareTriple(i+1, tracePrecondition, tracePostcondition, 
						interpolants, trace);
			 if (result == LBool.SAT) {
				 s_Logger.debug("Trace length: " + trace.length());
				 s_Logger.debug("Stmt: " + i);
				 s_Logger.debug("Pre_not_simplified: " + 
				 getInterpolantAtPosition(i+1, tracePrecondition, tracePostcondition, interpolantsNotSimplified));
				 s_Logger.debug("Post_not_simplified: " + 
						 getInterpolantAtPosition(i+2, tracePrecondition, tracePostcondition, interpolantsNotSimplified));
			 }
			 assert result == LBool.UNSAT || result == LBool.UNKNOWN;
		}
		result = isHoareTriple(interpolants.length, tracePrecondition, 
				tracePostcondition,	interpolants, trace);
		assert result == LBool.UNSAT || result == LBool.UNKNOWN;
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
				(cb instanceof StatementSequence);
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
