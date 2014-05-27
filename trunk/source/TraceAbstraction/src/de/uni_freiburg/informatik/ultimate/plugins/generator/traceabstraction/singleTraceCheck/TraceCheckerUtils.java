package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
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
	 * The sequence of interpolants returned by a TraceChecker contains neither
	 * the precondition nor the postcondition of the trace check.
	 * This auxiliary method allows one to access the precondition via the
	 * index -1 and to access the postcondition via the index 
	 * interpolants.lenth (first index after the interpolants array).
	 * 
	 * In the future we might also use negative indices to access pending
	 * contexts (therefore you should catch the Error throw by this method).
	 */
	public static IPredicate getInterpolant(int i, IPredicate precondition, 
			IPredicate[] interpolants, IPredicate postcondition) {
		if (i < -1) {
			throw new AssertionError("index beyond precondition");
		} else if (i == -1) {
			return precondition;
		} else if (i < interpolants.length) {
			return interpolants[i];
		} else if (i == interpolants.length) {
			return postcondition;
		} else {
			throw new AssertionError("index beyond postcondition");
		}
	}
	
}
