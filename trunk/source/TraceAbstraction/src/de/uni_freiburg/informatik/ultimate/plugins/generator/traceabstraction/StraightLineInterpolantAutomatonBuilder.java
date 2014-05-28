package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;

/**
 * Build an interpolant automaton whose shape is a straight line.
 * The input for this construction is a TraceChecker that has proven that
 * its trace is infeasible.
 * The result of this construction is a NestedWordAutomaton object that can 
 * still be modified by adding additional states or transitions.
 * The result has one initial state which is the precondition of the trace 
 * check, the result has one accepting/final state which is the postcondition
 * of the trace check, the result has one state for each interpolant,
 * the result has one transition for each CodeBlock in the trace.
 * The result accepts the word/trace of the trace check. IPredicates may occur
 * several times in the array of interpolants, hence the resulting automaton
 * may also have loops and accept more than a single word.
 * @author Matthias Heizmann
 *
 */
public class StraightLineInterpolantAutomatonBuilder {
	
	private final NestedWordAutomaton<CodeBlock, IPredicate> m_Result;
	
	public StraightLineInterpolantAutomatonBuilder(
			InCaReAlphabet<CodeBlock> alphabet,
			TraceChecker traceChecker,
			PredicateFactory predicateFactory) {
		if (traceChecker.isCorrect() != LBool.UNSAT) {
			throw new AssertionError("We can only build an interpolant "
					+ "automaton for correct/infeasible traces");
		}
		if (traceChecker.getInterpolants() == null) {
			throw new AssertionError("We can only build an interpolant "
					+ "automaton for which interpolants were computed");
		}
		m_Result =	new NestedWordAutomaton<CodeBlock, IPredicate>(
						alphabet.getInternalAlphabet(),
						alphabet.getCallAlphabet(),
						alphabet.getReturnAlphabet(),
						predicateFactory);
		addStatesAndTransitions(traceChecker, predicateFactory);
	}

	private void addStatesAndTransitions(TraceChecker traceChecker, PredicateFactory predicateFactory) { 

		m_Result.addState(true, false, traceChecker.getPrecondition());
		m_Result.addState(false, true, traceChecker.getPostcondition());
		NestedWord<CodeBlock> trace = (NestedWord<CodeBlock>) traceChecker.getTrace();
		for (int i=0; i<trace.length(); i++) {
			IPredicate pred = TraceCheckerUtils.getInterpolant(i-1, 
					traceChecker.getPrecondition(), 
					traceChecker.getInterpolants(), 
					traceChecker.getPostcondition());
			IPredicate succ = TraceCheckerUtils.getInterpolant(i, 
					traceChecker.getPrecondition(), 
					traceChecker.getInterpolants(), 
					traceChecker.getPostcondition());
			assert m_Result.getStates().contains(pred);
			if (!m_Result.getStates().contains(succ)) {
				m_Result.addState(false, false, succ);
			}
			if (trace.isCallPosition(i)) {
				m_Result.addCallTransition(pred, trace.getSymbol(i), succ);
			} else if (trace.isReturnPosition(i)) {
				assert !trace.isPendingReturn(i);
				int callPos = trace.getCallPosition(i);
				IPredicate hierPred = TraceCheckerUtils.getInterpolant(callPos-1, 
						traceChecker.getPrecondition(), 
						traceChecker.getInterpolants(), 
						traceChecker.getPostcondition());
				m_Result.addReturnTransition(pred, hierPred, trace.getSymbol(i), succ);
			} else {
				assert trace.isInternalPosition(i);
				m_Result.addInternalTransition(pred, trace.getSymbol(i), succ);
			}
		}
	}


	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return m_Result;
	}
	
}
