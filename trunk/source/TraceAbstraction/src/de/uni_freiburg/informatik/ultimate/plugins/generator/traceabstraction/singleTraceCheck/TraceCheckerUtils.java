package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck;

import java.util.ArrayList;
import java.util.List;
import java.util.SortedMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ParallelComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.SequentialComposition;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.StatementSequence;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Summary;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CoverageAnalysis.BackwardCoveringInformation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.MonolithicHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

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
	 * @param logger 
	 */
	public static BackwardCoveringInformation computeCoverageCapability(
			IUltimateServiceProvider services, 
			InterpolatingTraceChecker traceChecker, Logger logger) {
		NestedWord<CodeBlock> trace = NestedWord.nestedWord(traceChecker.getTrace());
		List<ProgramPoint> programPoints = getSequenceOfProgramPoints(trace);
		return computeCoverageCapability(services, traceChecker, programPoints, logger);
	}
	
	public static BackwardCoveringInformation computeCoverageCapability(
			IUltimateServiceProvider services, 
			InterpolatingTraceChecker traceChecker, List<ProgramPoint> programPoints, Logger logger) {
		if (traceChecker.isCorrect() != LBool.UNSAT) {
			throw new AssertionError("We can only build an interpolant "
					+ "automaton for correct/infeasible traces");
		}
		if (traceChecker.getInterpolants() == null) {
			throw new AssertionError("We can only build an interpolant "
					+ "automaton for which interpolants were computed");
		}
		CoverageAnalysis ca = new CoverageAnalysis(services, traceChecker, programPoints, logger);
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
		
		public InterpolantsPreconditionPostcondition(InterpolatingTraceChecker traceChecker) {
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
		
		public InterpolantsPreconditionPostcondition(IPredicate precondition,
				IPredicate postcondition, IPredicate[] interpolants) {
			super();
			m_Precondition = precondition;
			m_Postcondition = postcondition;
			m_Interpolants = interpolants;
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
	
	
	/***
	 * Checks whether the given sequence of predicates is inductive.
	 * For each i we check if  {predicates[i-1]} st_i {predicates[i]} is a 
	 * valid Hoare triple. If all triples are valid, we return true.
	 * Otherwise an exception is thrown.
	 */
	public static boolean checkInterpolantsInductivityForward(IPredicate[] interpolants, NestedWord<CodeBlock> trace, 
			IPredicate precondition, IPredicate postcondition, 
			SortedMap<Integer, IPredicate> pendingContexts, String computation, 
			SmtManager smtManager, ModifiableGlobalVariableManager mgvManager,
			Logger logger) {
		InterpolantsPreconditionPostcondition ipp = 
				new InterpolantsPreconditionPostcondition(precondition, postcondition, interpolants);
		Validity result;
		for (int i = 0; i <= interpolants.length; i++) {
			result = checkInductivityAtPosition(i, ipp, trace, pendingContexts, smtManager, mgvManager, logger);
			if (result != Validity.VALID && result != Validity.UNKNOWN) {
				throw new AssertionError("invalid Hoare triple in " + computation);
			}
		}
		return true;
	}
	
	/***
	 * Similar to the method checkInterpolantsInductivityForward.
	 * But here we start from the end. This ensures that we get the last
	 * Hoare triple that is invalid.
	 * 
	 * @see checkInterpolantsInductivityForward
	 */
	public static boolean checkInterpolantsInductivityBackward(IPredicate[] interpolants, NestedWord<CodeBlock> trace, 
			IPredicate precondition, IPredicate postcondition, 
			SortedMap<Integer, IPredicate> pendingContexts, String computation, 
			SmtManager smtManager, ModifiableGlobalVariableManager mgvManager,
			Logger logger) {
		InterpolantsPreconditionPostcondition ipp = 
				new InterpolantsPreconditionPostcondition(precondition, postcondition, interpolants);
		Validity result;
		for (int i = interpolants.length; i >= 0; i--) {
			result = checkInductivityAtPosition(i, ipp, trace, pendingContexts, smtManager, mgvManager, logger);
			if (result != Validity.VALID && result != Validity.UNKNOWN) {
				throw new AssertionError("invalid Hoare triple in " + computation);
			}
		}
		return true;
	}
	
	
	private static Validity checkInductivityAtPosition(int i,
			InterpolantsPreconditionPostcondition ipp,
			NestedWord<CodeBlock> trace,
			SortedMap<Integer, IPredicate> pendingContexts,
			SmtManager smtManager, ModifiableGlobalVariableManager mgvManager,
			Logger logger) {
		IHoareTripleChecker htc = new MonolithicHoareTripleChecker(smtManager);
		IPredicate predecessor = ipp.getInterpolant(i);
		IPredicate successor = ipp.getInterpolant(i+1);
		CodeBlock cb = trace.getSymbol(i);
		final Validity result;
		if (trace.isCallPosition(i)) {
			assert (cb instanceof Call) : "not Call at call position";
			result = htc.checkCall(predecessor, cb, successor);
			logger.info(new DebugMessage("{0}: Hoare triple '{'{1}'}' {2} '{'{3}'}' is {4}", 
					i, predecessor, cb, successor, result));
		} else if (trace.isReturnPosition(i)) {
			assert (cb instanceof Return) : "not Call at call position";
			IPredicate hierarchicalPredecessor;
			if (trace.isPendingReturn(i)) {
				hierarchicalPredecessor = pendingContexts.get(i);
			} else {
				int callPosition = trace.getCallPosition(i);
				hierarchicalPredecessor = ipp.getInterpolant(callPosition);
			}
			result = htc.checkReturn(predecessor, hierarchicalPredecessor, cb, successor);
			logger.info(new DebugMessage("{0}: Hoare quadruple '{'{1}'}' '{'{5}'}' {2} '{'{3}'}' is {4}", 
					i, predecessor, cb, successor, result, hierarchicalPredecessor));
		} else if (trace.isInternalPosition(i)) {
			assert (cb instanceof SequentialComposition) || (cb instanceof ParallelComposition)
			|| (cb instanceof StatementSequence) || (cb instanceof Summary);
			result = htc.checkInternal(predecessor, cb, successor);
			logger.info(new DebugMessage("{0}: Hoare triple '{'{1}'}' {2} '{'{3}'}' is {4}", 
					i, predecessor, cb, successor, result));
		} else {
			throw new AssertionError("unsupported position");
		}
		return result;
	}


	
}
