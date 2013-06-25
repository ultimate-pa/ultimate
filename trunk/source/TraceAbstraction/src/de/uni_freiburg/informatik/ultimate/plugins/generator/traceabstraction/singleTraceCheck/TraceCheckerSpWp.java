package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.io.PrintWriter;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

public class TraceCheckerSpWp extends TraceChecker {
	
	protected IPredicate[] m_InterpolantsSp;
	protected IPredicate[] m_InterpolantsWp;

	public TraceCheckerSpWp(SmtManager smtManager,
			ModifiableGlobalVariableManager modifiedGlobals,
			Map<String, ProgramPoint> proc2entry, PrintWriter debugPW) {
		super(smtManager, modifiedGlobals, proc2entry, debugPW);
	}

	@Override
	public IPredicate[] getInterpolants(Set<Integer> interpolatedPositions) {
		// some fields from superclass that you definitely need
//		m_Precondition.toString();
//		m_Postcondition.toString();
//		m_Trace.toString();
//		m_SmtManager.toString();
		
		if (!(interpolatedPositions instanceof AllIntegers)) {
			throw new UnsupportedOperationException();
		}
		IPredicate tracePrecondition = m_Precondition;
		IPredicate tracePostcondition = m_Postcondition;
		Word<CodeBlock> trace = m_Trace;
		forgetTrace();
		
		m_InterpolantsSp = new IPredicate[trace.length()-1];
		m_InterpolantsWp = new IPredicate[trace.length()-1];
		
		m_InterpolantsSp[0] = m_SmtManager.strongestPostcondition(
										tracePrecondition, trace.getSymbol(0));
		for (int i=1; i<m_InterpolantsSp.length; i++) {
			m_InterpolantsSp[i] = m_SmtManager.strongestPostcondition(
					m_InterpolantsSp[i-1], trace.getSymbol(i));
		}
		
		/*
		m_InterpolantsWp[m_InterpolantsWp.length-1] = m_SmtManager.weakestPrecondition(
				tracePostcondition, trace.getSymbol(m_InterpolantsWp.length));
		
		for (int i=m_InterpolantsWp.length-2; i>=0; i--) {
			m_InterpolantsWp[i] = m_SmtManager.weakestPrecondition(
					m_InterpolantsSp[i+1], trace.getSymbol(i));
		}*/
		

		
		checkInterpolantsCorrect(m_InterpolantsSp, trace, tracePrecondition, tracePostcondition);
		// checkInterpolantsCorrect(m_InterpolantsWp, trace, tracePrecondition, tracePostcondition);
		
		return m_InterpolantsSp;
	}
	
	
	void checkInterpolantsCorrect(IPredicate[] interpolants, Word<CodeBlock> trace, 
								  IPredicate tracePrecondition, 
								  IPredicate tracePostcondition) {
		LBool result;
		result = isHoareTriple(tracePrecondition, trace.getSymbol(0), interpolants[0]);
		assert result == LBool.UNSAT || result == LBool.UNKNOWN;
		for (int i=0; i<interpolants.length-1; i++) {
			 result = isHoareTriple(interpolants[i], 
					 trace.getSymbol(i+1), interpolants[i+1]);
				assert result == LBool.UNSAT || result == LBool.UNKNOWN;
		}
		result = isHoareTriple(interpolants[interpolants.length-1], 
				trace.getSymbol(interpolants.length), tracePostcondition);
		assert result == LBool.UNSAT || result == LBool.UNKNOWN;
	}
	
	
	
	LBool isHoareTriple(IPredicate precondition, CodeBlock cb, IPredicate postcondition) {
		EdgeChecker ec = new EdgeChecker(m_SmtManager, m_ModifiedGlobals);
		ec.assertCodeBlock(cb);
		ec.assertPrecondition(precondition);
		LBool result = ec.postInternalImplies(postcondition);
		ec.unAssertPrecondition();
		ec.unAssertCodeBlock();
		s_Logger.debug("Hoare triple " + precondition + ", " + cb + ", " 
											+ postcondition + " is " + result);
		return result;
	}
	
	
	

}
