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
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerSpWp;

public class TwoTrackInterpolantAutomatonBuilder {
	
	private final TraceCheckerSpWp m_TraceCheckerSpWp;
	
	private final NestedWord<CodeBlock> m_NestedWord;
	private ArrayList<IPredicate> m_StateSequence;
	NestedWordAutomaton<CodeBlock, IPredicate> m_TTIA;
	private final SmtManager m_SmtManager;
	
	private NestedWordAutomaton<CodeBlock, IPredicate> m_Result;
	
	public TwoTrackInterpolantAutomatonBuilder(
			IRun<CodeBlock,IPredicate> nestedRun,
			SmtManager smtManager,
			TraceChecker traceChecker) {
		if (!(traceChecker instanceof TraceCheckerSpWp)) {
			throw new UnsupportedOperationException("Wrong trace checker");
		}
		m_TraceCheckerSpWp = (TraceCheckerSpWp) traceChecker;
		m_NestedWord = NestedWord.nestedWord(nestedRun.getWord());
		m_SmtManager = smtManager;
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
		
//		assert(m_NestedWord.length()-1==m_TraceCheckerSpWp.getI);
//		String interpolantAutomatonType;
//		switch (m_AdditionalEdges) {
//		case SINGLETRACE:
//			interpolantAutomatonType = 
//				"Constructing interpolant automaton without backedges";
//			break;
//		case CANONICAL:
//			interpolantAutomatonType = 
//				"Constructing canonical interpolant automaton";
//			break;
//		case TOTALINTERPOLATION:
//			interpolantAutomatonType = 
//				"Constructing eager interpolant automaton"; 
//			break;
//		default:
//			throw new IllegalArgumentException();
//			
//		}
//		if (m_SelfloopAtInitial) {
//			interpolantAutomatonType += ", with selfloop in true state";
//		}
//		if (m_SelfloopAtFinal) {
//			interpolantAutomatonType += ", with selfloop in false state";
//		}
//		s_Logger.info(interpolantAutomatonType);

		m_TTIA = new NestedWordAutomaton<CodeBlock, IPredicate>(
				internalAlphabet,
				callAlphabet,
				returnAlphabet,
				tAContentFactory);
		{
			m_TTIA.addState(true, false, m_TraceCheckerSpWp.getPrecondition());
//			List<Integer> occurrence = new ArrayList<Integer>();
//			occurrence.add(0);
//			ProgramPoint pp = getProgramPointAtPosition(0);
//			m_ProgramPoint2Occurence.put(pp,occurrence);
		}
		m_TTIA.addState(false, true, m_TraceCheckerSpWp.getPostcondition());
		
		for (int i=0; i<m_NestedWord.length(); i++) {
			// TODO: Is it really necessary, in our setting an automaton has only one initial,
			// and final state, namely initial = {true} and final={false}
			boolean isFinal = isFalsePredicate(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
			if (!m_TTIA.getStates().contains(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i))) {
				m_TTIA.addState(false, isFinal, m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
			}

			addTransition(m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i-1), i, m_TraceCheckerSpWp.getInterpolanstsSPAtPosition(i));
			
			isFinal = isFalsePredicate(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
			if (!m_TTIA.getStates().contains(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i))) {
				m_TTIA.addState(false, isFinal, m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
			}

			addTransition(m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i-1), i, m_TraceCheckerSpWp.getInterpolanstsWPAtPosition(i));
		}
			
//			if(m_AdditionalEdges == InterpolantAutomaton.CANONICAL) {
//				ProgramPoint pp = getProgramPointAtPosition(i-1);
//				List<Integer> occurrence = m_ProgramPoint2Occurence.get(pp);
//				if (occurrence == null) {
//					occurrence = new ArrayList<Integer>();
//					m_ProgramPoint2Occurence.put(pp, occurrence);
//				}
//				else {
//					for (int occur : occurrence) {
//						surveyBackedge(i-1, occur);
//					}
//				}
//				occurrence.add(i-1);
//			}
//		}
//		
//		
//		if (m_SelfloopAtInitial) {
//			for (CodeBlock symbol : internalAlphabet) {
//				m_IA.addInternalTransition(
//								getInterpolant(-1), symbol, getInterpolant(-1));
//			}
//			for (CodeBlock symbol : callAlphabet) {
//				m_IA.addCallTransition(
//								getInterpolant(-1), symbol, getInterpolant(-1));
//			}
//			for (CodeBlock symbol : returnAlphabet) {
//				m_IA.addReturnTransition(
//				  getInterpolant(-1),getInterpolant(-1),symbol,getInterpolant(-1));
//				for (Integer pos : m_AlternativeCallPredecessors.keySet()) {
//					for (IPredicate hier : 
//									m_AlternativeCallPredecessors.get(pos)) {
//						m_IA.addReturnTransition(
//							getInterpolant(-1), hier, symbol, getInterpolant(-1));
//					}
//				}
//
//			}
//			
//		}
//		
//		if (m_SelfloopAtFinal) {
//			for (CodeBlock symbol : internalAlphabet) {
//				m_IA.addInternalTransition(m_FalsePredicate, symbol, m_FalsePredicate);
//			}
//			for (CodeBlock symbol : callAlphabet) {
//				m_IA.addCallTransition(m_FalsePredicate, symbol, m_FalsePredicate);
//			}
//			for (CodeBlock symbol : returnAlphabet) {
//				m_IA.addReturnTransition(
//						m_FalsePredicate, m_FalsePredicate, symbol, m_FalsePredicate);
//				for (Integer pos : m_AlternativeCallPredecessors.keySet()) {
//					for (IPredicate hier : 
//									m_AlternativeCallPredecessors.get(pos)) {
//						m_IA.addReturnTransition(
//								m_FalsePredicate, hier, symbol, m_FalsePredicate);
//					}
//				}
//			}
//		}
//		
//		s_Logger.info("Checked inductivity of " +
//				(m_Unsat+m_Sat+m_Unknown+m_Trivial) +	" backedges. " + 
//				m_Unsat + " proven. " + 
//				m_Sat + " refuted. " + 
//				m_Unknown + " times theorem prover too weak." +
//				m_Trivial + " trivial.");
//		
//		if (m_AdditionalEdges == InterpolantAutomaton.TOTALINTERPOLATION) {
//			throw new UnsupportedOperationException();
//		}
		return m_TTIA;
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
		return m_Result;
	}

}
