package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;

public class TwoTrackInterpolantAutomatonBuilder {
	
	private final TraceCheckerSpWp m_TraceCheckerSpWp;
	
	private final NestedWord<CodeBlock> m_NestedWord;
//	private ArrayList<IPredicate> m_StateSequence;
	NestedWordAutomaton<CodeBlock, IPredicate> m_TTIA;
	private final SmtManager m_SmtManager;
	private static boolean m_TotalTransitions = true;
	
	
	public TwoTrackInterpolantAutomatonBuilder(
			IRun<CodeBlock,IPredicate> nestedRun,
			SmtManager smtManager,
			TraceChecker traceChecker,
			IAutomaton<CodeBlock, IPredicate> abstraction) {
		if (!(traceChecker instanceof TraceCheckerSpWp)) {
			throw new UnsupportedOperationException("Wrong trace checker");
		}
		m_TraceCheckerSpWp = (TraceCheckerSpWp) traceChecker;
		m_NestedWord = NestedWord.nestedWord(nestedRun.getWord());
		m_SmtManager = smtManager;
		m_TTIA = buildTwoTrackInterpolantAutomaton(abstraction, abstraction.getStateFactory());
	}
	
	public NestedWordAutomaton<CodeBlock, IPredicate> 
	buildTwoTrackInterpolantAutomaton(IAutomaton<CodeBlock, IPredicate> abstraction,
			StateFactory<IPredicate> tAContentFactory) {
		Set<CodeBlock> internalAlphabet = abstraction.getAlphabet();
		Set<CodeBlock> callAlphabet = new HashSet<CodeBlock>(0);
		Set<CodeBlock> returnAlphabet = new HashSet<CodeBlock>(0);

		if (abstraction instanceof INestedWordAutomatonSimple) {
			INestedWordAutomatonSimple<CodeBlock, IPredicate> abstractionAsNwa = (INestedWordAutomatonSimple<CodeBlock, IPredicate>) abstraction;
			callAlphabet = abstractionAsNwa.getCallAlphabet();
			returnAlphabet = abstractionAsNwa.getReturnAlphabet();
		}
		
		NestedWordAutomaton<CodeBlock, IPredicate> nwa = new NestedWordAutomaton<CodeBlock, IPredicate>(
				internalAlphabet, callAlphabet, returnAlphabet, tAContentFactory);
		
		// 1. Ensure that forward predicates has been computed.
		assert m_TraceCheckerSpWp.forwardsPredicatesComputed() : "Forward predicates has not been computed!" ;
		// 2. Ensure that backward predicates has been computed.
		assert m_TraceCheckerSpWp.backwardsPredicatesComputed() : "Backward predicates has not been computed" ;
		
		nwa.addState(true, false, m_TraceCheckerSpWp.getPrecondition());
		nwa.addState(false, true, m_TraceCheckerSpWp.getPostcondition());
		
		// Add states, which contains the predicates computed via SP, WP.
		addStatesAccordingToPredicates(nwa);
		addBasicTransitions(nwa);
		
		if (m_TotalTransitions) {
			addTotalTransitionsNaively(nwa);
		}
		
			
		return nwa;
	}
	
	/**
	 * Add a state for each forward predicate and for each backward predicate.
	 * @param nwa - the automaton to which the states are added
	 */
	private void addStatesAccordingToPredicates(NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		for (int i=0; i < m_NestedWord.length() - 1; i++) {
			// 1. Add a state which contains the predicate computed via SP
			boolean isFinal = isFalsePredicate(m_TraceCheckerSpWp.getForwardPredicateAtPosition(i));
			if (!nwa.getStates().contains(m_TraceCheckerSpWp.getForwardPredicateAtPosition(i))) {
				nwa.addState(false, isFinal, m_TraceCheckerSpWp.getForwardPredicateAtPosition(i));
			}
			// 2. Add a state which contains the predicate computed via WP
			isFinal = isFalsePredicate(m_TraceCheckerSpWp.getBackwardPredicateAtPosition(i));
			if (!nwa.getStates().contains(m_TraceCheckerSpWp.getBackwardPredicateAtPosition(i))) {
				nwa.addState(false, isFinal, m_TraceCheckerSpWp.getBackwardPredicateAtPosition(i));
			}
		}
	}
	
	/**
	 * Add basic transitions in 3 steps.
	 * 1. For each predicate type add a transition from the precondition to the first predicate.
	 * (i.e. add transition (preCondition, st_0, FP_0), add transition (preCondition, st_0, BP_0))
	 * 2. For each predicate type add a transition from the previous predicate to the current predicate.
	 * (i.e. add transition (FP_i-1, st_i, FP_i), add transition (BP_i-1, st_i, BP_i))
	 * 3. For each predicate type add a transition from the last predicate to the post-condition.
	 * (i.e. add transition (FP_n-1, st_n, postCondition), add transition (BP_n-1, st_n, postCondition))
	 * @param nwa - the automaton to which the basic transition are added
	 */
	private void addBasicTransitions(NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		// 1. For each predicate type add a transition from the precondition to the first predicate.
		addTransition(nwa, m_TraceCheckerSpWp.getPrecondition(), 0,
				m_TraceCheckerSpWp.getForwardPredicateAtPosition(0), true);

		addTransition(nwa, m_TraceCheckerSpWp.getPrecondition(), 0,
				m_TraceCheckerSpWp.getBackwardPredicateAtPosition(0), false);
		// 2. For each predicate type add a transition from the previous predicate to the current predicate.
		for (int i = 1; i < m_NestedWord.length() - 1; i++) {
			addTransition(nwa, m_TraceCheckerSpWp.getForwardPredicateAtPosition(i-1), i,
					m_TraceCheckerSpWp.getForwardPredicateAtPosition(i), true);
			addTransition(nwa, m_TraceCheckerSpWp.getBackwardPredicateAtPosition(i-1), i,
					m_TraceCheckerSpWp.getBackwardPredicateAtPosition(i), false);
		}
		// 3. For each predicate type add a transition from the last predicate to the post-condition.
		addTransition(nwa, m_TraceCheckerSpWp.getForwardPredicateAtPosition(m_NestedWord.length()-2), m_NestedWord.length()-1,
				m_TraceCheckerSpWp.getPostcondition(), true);
		addTransition(nwa, m_TraceCheckerSpWp.getBackwardPredicateAtPosition(m_NestedWord.length()-2), m_NestedWord.length()-1,
				m_TraceCheckerSpWp.getPostcondition(), false);
		
		
	}
	
	private boolean selfLoopAllowed(IPredicate p1, int symbolPos) {
		return transitionFromSPtoWPOrVVAllowed(p1, symbolPos, p1, true);
	}
	
	/**
	 * This is a naive strategy to add transitions between the two interpolant types.
	 * Transitions are added as follows:
	 * 1. For each forwards predicate FP_i: 
	 * 2.     for each backwards predicate BP_j:
	 * 3.          try to add the transition (FP_i, st_j, BP_j)
	 * 4.          try to add the transition (BP_j, st_j, FP_i) 
	 * @param nwa - the automaton to which the transitions are added.
	 */
	private void addTotalTransitionsNaively(NestedWordAutomaton<CodeBlock, IPredicate> nwa) {
		for (int i = 0; i < m_NestedWord.length(); i++) {
			IPredicate fp_i = m_TraceCheckerSpWp.getForwardPredicateAtPosition(i);
			for (int j = 0; j < m_NestedWord.length(); j++) {
				IPredicate bp_j = m_TraceCheckerSpWp.getBackwardPredicateAtPosition(j); 
				if (transitionFromSPtoWPOrVVAllowed(fp_i, j, bp_j, true)) {
					addTransition(nwa, fp_i, j, bp_j, true);
				}
				if (transitionFromSPtoWPOrVVAllowed(bp_j, j, fp_i, false)) {
					addTransition(nwa, bp_j, j, fp_i, false);
				}
			}
		}
	}
	
	/**
	 * Checks whether we are allowed to add a transition from a state annotated with the assertion p1 computed via
	 * SP (or WP)  with the statement obtained by symbolPos to a state annotated with the assertion p2 computed via WP (or SP).
	 * The boolean variable fromSPToWp indicates which direction we want to check, if it is true, then p1 is computed
	 * via SP and p2 via WP, else the other way around.
	 */
	private boolean transitionFromSPtoWPOrVVAllowed(IPredicate p1, int symbolPos, IPredicate p2, boolean fromSPToWP) {
		CodeBlock statement = m_NestedWord.getSymbol(symbolPos);
		if (m_NestedWord.isCallPosition(symbolPos)) {
			return (m_SmtManager.isInductiveCall(p1, (Call) statement, p2) == LBool.UNSAT);
		} else if (m_NestedWord.isReturnPosition(symbolPos)) {
			int callPos= m_NestedWord.getCallPosition(symbolPos);
			IPredicate callerPred = null;
			if (fromSPToWP) {
				m_TraceCheckerSpWp.getForwardPredicateAtPosition(callPos-1);
			} else {
				callerPred = m_TraceCheckerSpWp.getBackwardPredicateAtPosition(callPos-1);
			}
			return (m_SmtManager.isInductiveReturn(p1, callerPred,(Return) statement, p2) == LBool.UNSAT);
		} else {
			return (m_SmtManager.isInductive(p1, statement, p2) == LBool.UNSAT);
		}
	}
	
	
	/**
	 * TODO: What if the post-condition is not the "False-Predicate"?
	 * @param p
	 * @return
	 */
	private boolean isFalsePredicate(IPredicate p) {
		if (p == m_TraceCheckerSpWp.getPostcondition()) {
			return true;
		} else {
			assert SmtManager.isDontCare(p) || p.getFormula() != m_SmtManager.getScript().term("false");
			return false;
		}
	}
	
	
	private void addTransition(NestedWordAutomaton<CodeBlock, IPredicate> nwa, 
			IPredicate pred, int symbolPos, IPredicate succ, boolean forwardsPredicate) {
		CodeBlock symbol = m_NestedWord.getSymbol(symbolPos);
		if (m_NestedWord.isCallPosition(symbolPos)) {
			nwa.addCallTransition(pred, symbol, succ);
//			if (getInterpolant(prePos) != getInterpolant(symbolPos)) {
//				addAlternativeCallPredecessor(symbolPos, getInterpolant(prePos));
//			}
		}
		else if (m_NestedWord.isReturnPosition(symbolPos)) {
			int callPos= m_NestedWord.getCallPosition(symbolPos);
			IPredicate hier = null;
			if (forwardsPredicate) {
				hier = m_TraceCheckerSpWp.getForwardPredicateAtPosition(callPos-1);
			} else {
				hier = m_TraceCheckerSpWp.getBackwardPredicateAtPosition(callPos-1);
			}
			nwa.addReturnTransition(pred, hier, symbol, succ);
//			if(m_AdditionalEdges == InterpolantAutomaton.CANONICAL) {
//				addAlternativeReturnTransitions(pred, callPos, symbol, succ);
//			}
		}
		else {
			nwa.addInternalTransition(pred, symbol,  succ);
		}
	}
	
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return m_TTIA;
	}

}
