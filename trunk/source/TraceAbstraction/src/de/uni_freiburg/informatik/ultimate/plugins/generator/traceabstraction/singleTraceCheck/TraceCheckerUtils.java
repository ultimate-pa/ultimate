package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;

/**
 * Class that contains static methods that are related to the TraceChecker 
 * @author Matthias Heizmann
 *
 */
public class TraceCheckerUtils {
	
	/**
	 * Given a trace cb_0,...,cb_n returns the sequence of ProgramPoints 
	 * that corresponds to this trace. This is the sequence
	 * pp_0,...,pp_{n+1} such that
	 * <ul>
	 * <li> pp_i is the ProgramPoint before CodeBlock cb_i, and
	 * <li> pp_{i+1} is the ProgramPoint after CodeBlock cb_i.
	 * </ul>  
	 */
	public static List<ProgramPoint> getSequenceOfProgramPoints(
											NestedWord<CodeBlock> trace) {
		List<ProgramPoint> result = new ArrayList<ProgramPoint>();
		for (CodeBlock cb : trace) {
			ProgramPoint pp = (ProgramPoint) cb.getSource();
			result.add(pp);
		}
		CodeBlock cb = trace.getSymbol(trace.length()-1);
		ProgramPoint pp = (ProgramPoint) cb.getTarget();
		result.add(pp);
		return result;
	}
	
	/**
	 * Variant of computeCoverageCapability where the sequence of ProgramPoints
	 * is not a parameter but computed from the trace.
	 */
	public static BackwardCoveringInformation computeCoverageCapability(
			TraceChecker traceChecker) {
		NestedWord<CodeBlock> trace = NestedWord.nestedWord(traceChecker.getTrace());
		List<ProgramPoint> programPoints = getSequenceOfProgramPoints(trace);
		return computeCoverageCapability(traceChecker, programPoints);
	}
	
	public static BackwardCoveringInformation computeCoverageCapability(
			TraceChecker traceChecker, List<ProgramPoint> programPoints) {
		if (traceChecker.isCorrect() != LBool.UNSAT) {
			throw new AssertionError("We can only build an interpolant "
					+ "automaton for correct/infeasible traces");
		}
		if (traceChecker.getInterpolants() == null) {
			throw new AssertionError("We can only build an interpolant "
					+ "automaton for which interpolants were computed");
		}
		CoverageAnalysis ca = new CoverageAnalysis(traceChecker, programPoints);
		ca.analyze();
		return ca.getBackwardCoveringInformation();
	}
	
	
	/**
	 * The sequence of interpolants returned by a TraceChecker contains neither
	 * the precondition nor the postcondition of the trace check.
	 * This auxiliary class allows one to access the precondition via the
	 * index 0 and to access the postcondition via the index 
	 * interpolants.lenth+1 (first index after the interpolants array).
	 * All other indices are shifted by one.
	 * 
	 * In the future we might also use negative indices to access pending
	 * contexts (therefore you should not catch the Error throw by the 
	 * getInterpolant method).
	 */
	public static class InterpolantsPreconditionPostcondition {
		private final IPredicate m_Precondition;
		private final IPredicate m_Postcondition;
		private final IPredicate[] m_Interpolants;
		
		public InterpolantsPreconditionPostcondition(TraceChecker traceChecker) {
			if (traceChecker.isCorrect() != LBool.UNSAT) {
				throw new AssertionError("We can only build an interpolant "
						+ "automaton for correct/infeasible traces");
			}
			if (traceChecker.getInterpolants() == null) {
				throw new AssertionError("We can only build an interpolant "
						+ "automaton for which interpolants were computed");
			}
			m_Precondition = traceChecker.getPrecondition();
			m_Postcondition = traceChecker.getPostcondition();
			m_Interpolants = traceChecker.getInterpolants();
		}
		
		public IPredicate getInterpolant(int i) {
			if (i < 0) {
				throw new AssertionError("index beyond precondition");
			} else if (i == 0) {
				return m_Precondition;
			} else if (i <= m_Interpolants.length) {
				return m_Interpolants[i-1];
			} else if (i == m_Interpolants.length+1) {
				return m_Postcondition;
			} else {
				throw new AssertionError("index beyond postcondition");
			}
		}
	}
	
}
