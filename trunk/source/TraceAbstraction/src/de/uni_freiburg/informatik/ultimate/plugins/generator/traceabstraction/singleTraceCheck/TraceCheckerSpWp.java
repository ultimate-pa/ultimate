package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.io.PrintWriter;
import java.lang.reflect.Array;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class TraceCheckerSpWp extends TraceChecker {
	
	protected IPredicate[] m_InterpolantsSp;
	protected IPredicate[] m_InterpolantsWp;
	
	private static boolean m_useUnsatCore = false;

	public TraceCheckerSpWp(SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			Map<String, ProgramPoint> proc2entry, PrintWriter debugPW) {
		super(smtManager, modifiedGlobals, proc2entry, debugPW);
	}

	@Override
	public IPredicate[] getInterpolants(Set<Integer> interpolatedPositions) {
		// return getInterpolantsIgnoringCallAndReturn(interpolatedPositions);
		if (m_useUnsatCore) {
			return getInterpolantsWithUsageOfUnsatCore(interpolatedPositions);
		} else {
			return getInterpolantsWithoutUsageOfUnsatCore(interpolatedPositions);
		}
	}
	
	private IPredicate[] getInterpolantsWithUsageOfUnsatCore(Set<Integer> interpolatedPositions) {
		
		Term[] unsat_core = m_SmtManager.getScript().getUnsatCore();
		
		Set<Term> unsat_coresAsSet = new HashSet<Term>(Arrays.asList(unsat_core));
		
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		m_PredicateBuilder.declarePredicate(tracePrecondition);
		m_PredicateBuilder.declarePredicate(tracePostcondition);
		Word<CodeBlock> trace = m_Trace;
		Set<CodeBlock> codeBlocksInUnsatCore = new HashSet<CodeBlock>();
		
		forgetTrace();
		// Filter out the statements, which doesn't occur in the unsat core.
		for (int i = 0; i < trace.length(); i++) {
			if (isInUnsatCore(i, unsat_coresAsSet)) {
				codeBlocksInUnsatCore.add(trace.getSymbol(i));
			}
		}


		m_InterpolantsSp = new IPredicate[trace.length()-1];
		m_InterpolantsWp = new IPredicate[trace.length()-1];
		IPredicate lastlyComputedPred = tracePrecondition;
		IPredicate predOfLastStmtInUnsatCore = tracePrecondition;
		
		s_Logger.debug("Computing strongest postcondition for given trace ...");

		for (int i=0; i<m_InterpolantsSp.length; i++) {
			if (trace.getSymbol(i) instanceof Call) {
				if (codeBlocksInUnsatCore.contains(trace.getSymbol(i))) {
					IPredicate p = m_SmtManager.strongestPostcondition(
							predOfLastStmtInUnsatCore, (Call) trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
							new HashSet<String>(Arrays.asList(p.getProcedures())));
					predOfLastStmtInUnsatCore = m_InterpolantsSp[i];
					lastlyComputedPred = m_InterpolantsSp[i];
				} else {
					IPredicate p = m_SmtManager.strongestPostconditionSpecial(
							lastlyComputedPred, trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
							new HashSet<String>(Arrays.asList(p.getProcedures())));
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
					m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
							new HashSet<String>(Arrays.asList(p.getProcedures())));
					predOfLastStmtInUnsatCore = m_InterpolantsSp[i];
					lastlyComputedPred = m_InterpolantsSp[i];
				} else {
					// TODO: Probably, we also have to define a special method for Return and Call statement.
					IPredicate p = m_SmtManager.strongestPostconditionSpecial(
							lastlyComputedPred, trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
							new HashSet<String>(Arrays.asList(p.getProcedures())));
					lastlyComputedPred = m_InterpolantsSp[i];
				}
				
			} else {
				if (codeBlocksInUnsatCore.contains(trace.getSymbol(i))) {
					IPredicate p = m_SmtManager.strongestPostcondition(
							predOfLastStmtInUnsatCore, trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
							new HashSet<String>(Arrays.asList(p.getProcedures())));
					predOfLastStmtInUnsatCore = m_InterpolantsSp[i];
					lastlyComputedPred = m_InterpolantsSp[i];
				} else {
					IPredicate p = m_SmtManager.strongestPostconditionSpecial(
							lastlyComputedPred, trace.getSymbol(i));
					m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
							new HashSet<String>(Arrays.asList(p.getProcedures())));
					lastlyComputedPred = m_InterpolantsSp[i];
				}
			}
		}

		
		/*s_Logger.debug("Computing weakest precondition for given trace ...");
		m_InterpolantsWp[m_InterpolantsWp.length-1] = m_SmtManager.weakestPrecondition(
				tracePostcondition, trace.getSymbol(m_InterpolantsWp.length));
		
		for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
			m_InterpolantsWp[i] = m_SmtManager.weakestPrecondition(
					m_InterpolantsWp[i+1], trace.getSymbol(i+1));
		}
		*/

		s_Logger.debug("Checking strongest postcondition...");
		checkInterpolantsCorrect(m_InterpolantsSp, trace, tracePrecondition, tracePostcondition);
		/*s_Logger.debug("Checking weakest precondition...");
		checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition, tracePostcondition);*/
		
		return m_InterpolantsSp;
	}
	
	private IPredicate[] getInterpolantsWithoutUsageOfUnsatCore(Set<Integer> interpolatedPositions) {
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		m_PredicateBuilder.declarePredicate(tracePrecondition);
		m_PredicateBuilder.declarePredicate(tracePostcondition);
		
		Word<CodeBlock> trace = m_Trace;
		
		forgetTrace();
		m_InterpolantsSp = new IPredicate[trace.length()-1];
		m_InterpolantsWp = new IPredicate[trace.length()-1];
		
		s_Logger.debug("Computing strongest postcondition for given trace ...");
		
		if (trace.getSymbol(0) instanceof Call) {
			IPredicate p = m_SmtManager.strongestPostcondition(
					tracePrecondition, (Call) trace.getSymbol(0));
			m_InterpolantsSp[0] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
					new HashSet<String>(Arrays.asList(p.getProcedures())));
		} else {
			IPredicate p = m_SmtManager.strongestPostcondition(
					tracePrecondition, trace.getSymbol(0));
			m_InterpolantsSp[0] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
					new HashSet<String>(Arrays.asList(p.getProcedures())));
		}
		for (int i=1; i<m_InterpolantsSp.length; i++) {
			if (trace.getSymbol(i) instanceof Call) {
				IPredicate p = m_SmtManager.strongestPostcondition(
						m_InterpolantsSp[i-1], (Call) trace.getSymbol(i));
				m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
						new HashSet<String>(Arrays.asList(p.getProcedures())));
			} else if (trace.getSymbol(i) instanceof Return) {
				int call_pos = ((NestedWord<CodeBlock>)trace).getCallPosition(i);
				assert call_pos >= 0 && call_pos <= i : "Bad call position!";
				IPredicate callerPred = tracePrecondition;
				if (call_pos > 0) {
					callerPred = m_InterpolantsSp[call_pos - 1];
				}
				IPredicate p = m_SmtManager.strongestPostcondition(
						m_InterpolantsSp[i-1], callerPred, (Return) trace.getSymbol(i));
				m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
						new HashSet<String>(Arrays.asList(p.getProcedures())));
			} else {
				IPredicate p = m_SmtManager.strongestPostcondition(
						m_InterpolantsSp[i-1],trace.getSymbol(i));
				m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
						new HashSet<String>(Arrays.asList(p.getProcedures())));
			}
		}

		
		/*s_Logger.debug("Computing weakest precondition for given trace ...");
		m_InterpolantsWp[m_InterpolantsWp.length-1] = m_SmtManager.weakestPrecondition(
				tracePostcondition, trace.getSymbol(m_InterpolantsWp.length));
		
		for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
			m_InterpolantsWp[i] = m_SmtManager.weakestPrecondition(
					m_InterpolantsWp[i+1], trace.getSymbol(i+1));
		}*/
		

		s_Logger.debug("Checking strongest postcondition...");
		checkInterpolantsCorrect(m_InterpolantsSp, trace, tracePrecondition, tracePostcondition);
		/*s_Logger.debug("Checking weakest precondition...");
		checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition, tracePostcondition);*/
		
		return m_InterpolantsSp;
	}
	
	private IPredicate[] getInterpolantsIgnoringCallAndReturn(Set<Integer> interpolatedPositions) {
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		m_PredicateBuilder.declarePredicate(tracePrecondition);
		m_PredicateBuilder.declarePredicate(tracePostcondition);
		
		Word<CodeBlock> trace = m_Trace;
		
		forgetTrace();
		m_InterpolantsSp = new IPredicate[trace.length()-1];
		m_InterpolantsWp = new IPredicate[trace.length()-1];
		
		s_Logger.debug("Computing strongest postcondition for given trace ...");
		
		{
			IPredicate p = m_SmtManager.strongestPostcondition(
					tracePrecondition, trace.getSymbol(0));
			m_InterpolantsSp[0] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
					new HashSet<String>(Arrays.asList(p.getProcedures())));
		}
		for (int i=1; i<m_InterpolantsSp.length; i++) {
			IPredicate p = m_SmtManager.strongestPostcondition(
					m_InterpolantsSp[i-1],trace.getSymbol(i));
			m_InterpolantsSp[i] = m_PredicateBuilder.getOrConstructPredicate(p.getFormula(), p.getVars(),
					new HashSet<String>(Arrays.asList(p.getProcedures())));
		}

		
		/*s_Logger.debug("Computing weakest precondition for given trace ...");
		m_InterpolantsWp[m_InterpolantsWp.length-1] = m_SmtManager.weakestPrecondition(
				tracePostcondition, trace.getSymbol(m_InterpolantsWp.length));
		
		for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
			m_InterpolantsWp[i] = m_SmtManager.weakestPrecondition(
					m_InterpolantsWp[i+1], trace.getSymbol(i+1));
		}*/
		

		s_Logger.debug("Checking strongest postcondition...");
		checkInterpolantsCorrect(m_InterpolantsSp, trace, tracePrecondition, tracePostcondition);
		/*s_Logger.debug("Checking weakest precondition...");
		checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition, tracePostcondition);*/
		
		return m_InterpolantsSp;
	}
	
	/**
	 * Checks whether the term at position pos is contained in unsat_core.
	 */
	private boolean isInUnsatCore(int pos, Set<Term> unsat_core) {
		Term annotTerm = m_AnnotatedSsa.getTerms()[pos];
		return unsat_core.contains(annotTerm);
	}
	
	void checkInterpolantsCorrect(IPredicate[] interpolants, Word<CodeBlock> trace, 
								  IPredicate tracePrecondition, 
								  IPredicate tracePostcondition) {
		LBool result;
		result = isHoareTriple(0, tracePrecondition, tracePostcondition, 
				interpolants, trace);
		assert result == LBool.UNSAT || result == LBool.UNKNOWN;
		for (int i=0; i<interpolants.length-1; i++) {
			 result = isHoareTriple(i+1, tracePrecondition, tracePostcondition, 
						interpolants, trace);
				assert result == LBool.UNSAT || result == LBool.UNKNOWN;
		}
		result = isHoareTriple(interpolants.length, tracePrecondition, 
				tracePostcondition,	interpolants, trace);
		assert result == LBool.UNSAT || result == LBool.UNKNOWN;
	}
	
	IPredicate getInterpolantAtPosition(int i, IPredicate tracePrecondition,
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
	
	
	
	LBool isHoareTriple(int i, IPredicate tracePrecondition, 
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
			IPredicate callPredecessor = getInterpolantAtPosition(callPosition, 
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
