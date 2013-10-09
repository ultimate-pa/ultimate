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
			INestedWordAutomatonSimple<CodeBlock, IPredicate> nwa = (INestedWordAutomatonSimple<CodeBlock, IPredicate>) abstraction;
			callAlphabet = nwa.getCallAlphabet();
			returnAlphabet = nwa.getReturnAlphabet();
		}
		
		m_TTIA = new NestedWordAutomaton<CodeBlock, IPredicate>(
				internalAlphabet,
				callAlphabet,
				returnAlphabet,
				tAContentFactory);
		m_TTIA.addState(true, false, m_TraceCheckerSpWp.getPrecondition());
		m_TTIA.addState(false, true, m_TraceCheckerSpWp.getPostcondition());
		
		for (int i=0; i<m_NestedWord.length(); i++) {
			if (i < (m_NestedWord.length() - 1)) {
				if (m_TraceCheckerSpWp.interpolantsSPComputed()) {
				// 1. Add a state which contains the assertion computed via SP
					boolean isFinal = isFalsePredicate(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					if (!m_TTIA.getStates().contains(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i))) {
						m_TTIA.addState(false, isFinal, m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					}
				}
				// 2. Add a state which contains the assertion computed via WP
				if (m_TraceCheckerSpWp.interpolantsWPComputed()) {
					boolean isFinal = isFalsePredicate(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					if (!m_TTIA.getStates().contains(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i))) {
						m_TTIA.addState(false, isFinal, m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					}
				}
			}
			if (i == 0) {
				if (m_TraceCheckerSpWp.interpolantsSPComputed()) {
					addTransition(m_TraceCheckerSpWp.getPrecondition(), i,
							m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					// Try to add a self-loop labelled with stmt i on the current state 
					if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i,
								m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					}// Try to add a self-loop labelled with stmt (i+1) on the current state 
					else if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), (i+1),
								m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					}
				}
				
				
				if (m_TraceCheckerSpWp.interpolantsWPComputed()) {
					addTransition(m_TraceCheckerSpWp.getPrecondition(), i,
							m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					// Try to add a self-loop labelled with stmt i on the current state 
					if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i,
								m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					}// Try to add a self-loop labelled with stmt (i+1) on the current state 
					else if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), (i+1),
								m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					}
				}
				
			} else if (i == (m_NestedWord.length() - 1)) {
				if (m_TraceCheckerSpWp.interpolantsSPComputed()) {
					addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i-1), i,
							m_TraceCheckerSpWp.getPostcondition());
					// Try to add a self-loop labelled with stmt i on the current state 
					if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i,
								m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					}
				}
				if (m_TraceCheckerSpWp.interpolantsWPComputed()) {
					addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i-1), i,
							m_TraceCheckerSpWp.getPostcondition());
					// Try to add a self-loop labelled with stmt i on the current state 
					if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i,
								m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					}
				}
			} else {
				if (m_TraceCheckerSpWp.interpolantsSPComputed()) {
					addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i-1), i,
							m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i,
								m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					}// Try to add a self-loop labelled with stmt (i+1) on the current state 
					else if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), (i+1),
								m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					}
				}
				if (m_TraceCheckerSpWp.interpolantsWPComputed()) {
					addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i-1), i,
							m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					// Try to add a self-loop labelled with stmt i on the current state 
					if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i,
								m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					}// Try to add a self-loop labelled with stmt (i+1) on the current state 
					else if (selfLoopAllowed(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i)) {
						addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), (i+1),
								m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					}
				}
				// 1. Try to add a transition from state annotated with the assertion computed via SP to
				// to a state annotated with the assertion computed via WP.
				if (m_TraceCheckerSpWp.interpolantsSPComputed() && m_TraceCheckerSpWp.interpolantsWPComputed()) {
					if (transitionFromSPtoWPOrVVAllowed(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i),
							i,
							m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i),true)) { 
						addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i), i,
								m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
					}
				}
				// 2. Try to add a transition from state annotated with the assertion computed via WP to
				// to a state annotated with the assertion computed via SP.
				if (m_TraceCheckerSpWp.interpolantsSPComputed() && m_TraceCheckerSpWp.interpolantsWPComputed()) {
					if (transitionFromSPtoWPOrVVAllowed(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i),
							i,
							m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i),false)) { 
						addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i), i,
								m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
					}
				}
			}
		}
			
		return m_TTIA;
	}
	
	private boolean selfLoopAllowed(IPredicate p1, int symbolPos) {
		return transitionFromSPtoWPOrVVAllowed(p1, symbolPos, p1, true);
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
			IPredicate callerPred = m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(callPos-1);
			if (!fromSPToWP) {
				callerPred = m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(callPos-1);
			}
			return (m_SmtManager.isInductiveReturn(p1, callerPred,(Return) statement, p2) == LBool.UNSAT);
		} else {
			return (m_SmtManager.isInductive(p1, statement, p2) == LBool.UNSAT);
		}
	}
	
	private boolean isFalsePredicate(IPredicate p) {
		if (p == m_TraceCheckerSpWp.getPostcondition()) {
			return true;
		} else {
			assert SmtManager.isDontCare(p) || p.getFormula() != m_SmtManager.getScript().term("false");
			return false;
		}
	}
	
	private void addTransition(IPredicate pred, int symbolPos, IPredicate succ) {
		CodeBlock symbol = m_NestedWord.getSymbol(symbolPos);
		if (m_NestedWord.isCallPosition(symbolPos)) {
			m_TTIA.addCallTransition(pred, symbol, succ);
//			if (getInterpolant(prePos) != getInterpolant(symbolPos)) {
//				addAlternativeCallPredecessor(symbolPos, getInterpolant(prePos));
//			}
		}
		else if (m_NestedWord.isReturnPosition(symbolPos)) {
			int callPos= m_NestedWord.getCallPosition(symbolPos);
			IPredicate hier = m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(callPos-1);
			m_TTIA.addReturnTransition(pred, hier, symbol, succ);
//			if(m_AdditionalEdges == InterpolantAutomaton.CANONICAL) {
//				addAlternativeReturnTransitions(pred, callPos, symbol, succ);
//			}
		}
		else {
			m_TTIA.addInternalTransition(pred, symbol,  succ);
		}
	}
	
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return m_TTIA;
	}

}
