package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;

public class TotalInterpolationAutomatonBuilder {
	
	private ArrayList<IPredicate> m_StateSequence;
	private final IPredicate[] m_Interpolants;
	private final NestedWordAutomaton<CodeBlock, IPredicate> m_IA;
	private final PredicateUnifier m_PredicateUnifier;
	private final TraceChecker m_TraceChecker;
	private final INestedWordAutomaton<CodeBlock, IPredicate> m_Abstraction;
	
	private final SmtManager m_SmtManager;
	
//	private final IPredicate m_TruePredicate;
//	private final IPredicate m_FalsePredicate;
	private AutomatonEpimorphism<IPredicate> m_Epimorphism;
	public TotalInterpolationAutomatonBuilder(
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			ArrayList<IPredicate> stateSequence, TraceChecker traceChecker,
			SmtManager smtManager, PredicateFactory predicateFactory) throws OperationCanceledException {
		super();
		m_StateSequence = stateSequence;
		m_TraceChecker = traceChecker;
		m_SmtManager = smtManager;
		m_Interpolants = traceChecker.getInterpolants();
		m_PredicateUnifier = traceChecker.getPredicateUnifier();
		m_Abstraction = abstraction;
		m_IA = (new StraightLineInterpolantAutomatonBuilder(
				abstraction.getInternalAlphabet(), abstraction.getCallAlphabet(), 
				abstraction.getReturnAlphabet() , traceChecker, predicateFactory)).getResult();
		m_Epimorphism = constructInitialEpimorphism(stateSequence, traceChecker);
		for (IPredicate state : stateSequence) {
			for (OutgoingInternalTransition<CodeBlock, IPredicate> transition : m_Abstraction.internalSuccessors(state)) {
				startDfs(state, transition);
			}
		}
	}
	
	
	private void startDfs(IPredicate state,
			OutgoingInternalTransition<CodeBlock, IPredicate> transition) {
		new GraphDfs(null, state, transition);
	}


	private class GraphDfs {
		private final Set<IPredicate> m_Goal;
		private final Set<IPredicate> m_Visited = new HashSet<IPredicate>();
		private final Stack<Iterator<?>> m_IteratorStack = new Stack<Iterator<?>>();
		private final Stack<Transitionlet<CodeBlock, IPredicate>> m_TransitionStack = new Stack<Transitionlet<CodeBlock, IPredicate>>();
		private final Stack<IPredicate> m_StateStack = new Stack<IPredicate>();
		private final Stack<IPredicate> m_CallPredecessors = new Stack<IPredicate>();
		
		IPredicate m_CurrentPred;
		IPredicate m_CurrentSucc;
		Iterator<Transitionlet<CodeBlock, IPredicate>> m_CurrentIterator;
		Transitionlet<CodeBlock, IPredicate> m_CurrentTransition;
		
		
		
		public GraphDfs(Set<IPredicate> goal, IPredicate currentPred,
				Transitionlet<CodeBlock, IPredicate> initialTransition) {
			super();
			m_Goal = goal;
			m_CurrentPred = currentPred;
			m_CurrentTransition = initialTransition;
			m_CurrentIterator = null;
			m_CurrentSucc = getSuccessor(initialTransition);
		}
		
		private IPredicate getSuccessor(Transitionlet<CodeBlock, IPredicate> transition) {
			IPredicate result;
			if (transition instanceof OutgoingInternalTransition) {
				result = ((OutgoingInternalTransition<CodeBlock, IPredicate>) transition).getSucc();
			} else if (transition instanceof OutgoingCallTransition) {
				result = ((OutgoingCallTransition<CodeBlock, IPredicate>) transition).getSucc();
			} else if (transition instanceof OutgoingReturnTransition) {
				result = ((OutgoingReturnTransition<CodeBlock, IPredicate>) transition).getSucc();
			} else {
				throw new AssertionError("unsupported" + transition.getClass());
			}
			return result;
		}

		public void searchGoal() {
			while (!m_Goal.contains(m_CurrentSucc)) {
				m_Visited.add(m_CurrentSucc);
				push();
				getNextTransition();
				while(m_CurrentTransition == null) {
					if (getStackHeight() == 1) {
						// we never iterate over the initial Iterator.
						return;
					}
					pop();
					getNextTransition();
				}
				m_CurrentSucc = getSuccessor(m_CurrentTransition);
			}
		}
		
		private int getStackHeight() {
			assert allStacksHaveSameHeight();
			return m_StateStack.size();
		}
		
		private boolean allStacksHaveSameHeight() {
			boolean result = (m_StateStack.size() == m_IteratorStack.size());
			result &= (m_StateStack.size() == m_TransitionStack.size());
			return result;
		}
		
		private void push() {
			assert allStacksHaveSameHeight();
			m_TransitionStack.push(m_CurrentTransition);
			m_IteratorStack.push(m_CurrentIterator);
			m_StateStack.push(m_CurrentPred);
			if (m_CurrentTransition instanceof OutgoingCallTransition) {
				m_CallPredecessors.add(m_CurrentPred);
			}
			m_CurrentPred = m_CurrentSucc;
			m_CurrentTransition = null;
			m_CurrentIterator = null;
			m_CurrentSucc = null;
		}
		
		private void pop() {
			assert allStacksHaveSameHeight();
			m_CurrentSucc = m_CurrentPred;
			m_CurrentPred = m_StateStack.pop();
			if (m_CurrentTransition instanceof OutgoingCallTransition) {
				IPredicate callPred = m_CallPredecessors.pop();
				assert callPred == m_CurrentPred;
			}
			m_CurrentIterator = (Iterator<Transitionlet<CodeBlock, IPredicate>>) m_IteratorStack.pop();
			m_CurrentTransition = m_TransitionStack.pop();
		}
		
		public void getNextTransition() {
			if (m_CurrentIterator.hasNext()) {
				m_CurrentTransition = m_CurrentIterator.next();
			} else {
				if (m_CurrentTransition instanceof OutgoingInternalTransition) {
					switchIteratorInternalToCall();
					//TODO: implement
				}
			}
			if (m_CurrentTransition instanceof OutgoingInternalTransition) {
				m_CurrentTransition = getNextInternalTransition();
				if (m_CurrentTransition == null) {
					
				}
			}
			
		}
		
		public void switchIteratorInternalToCall() {
			assert !m_IteratorStack.peek().hasNext();
			m_IteratorStack.pop();
			IPredicate top = m_StateStack.peek();
			Iterator<OutgoingCallTransition<CodeBlock, IPredicate>> it = m_Abstraction.callSuccessors(top).iterator();
			m_IteratorStack.push(it);
		}
		
		public void switchIteratorCallToReturn() {
			assert !m_IteratorStack.peek().hasNext();
			m_IteratorStack.pop();
			IPredicate top = m_StateStack.peek();
			Iterator<OutgoingReturnTransition<CodeBlock, IPredicate>> it = m_Abstraction.returnSuccessors(top).iterator();
			m_IteratorStack.push(it);
		}
		
		public OutgoingInternalTransition<CodeBlock, IPredicate> getNextInternalTransition() {
			if (m_IteratorStack.peek().hasNext()) {
				return (OutgoingInternalTransition<CodeBlock, IPredicate>) m_IteratorStack.peek().next();
			} else {
				return null;
			}
		}
	}

	private AutomatonEpimorphism<IPredicate> constructInitialEpimorphism(List<IPredicate> stateSequence, TraceChecker traceChecker) {
		AutomatonEpimorphism<IPredicate> result = new AutomatonEpimorphism<>();
		for (int i=0; i<stateSequence.size(); i++) {
			IPredicate state = stateSequence.get(i);
			IPredicate interpolant = TraceCheckerUtils.getInterpolant(i-1, traceChecker.getPrecondition(), traceChecker.getInterpolants(), traceChecker.getPostcondition());
			result.insert(state, interpolant);
		}
		return result;
	}
	

}
