package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantAutomataBuilders;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.Stack;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.InCaReAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.Accepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.EdgeChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.INTERPOLATION;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

public class TotalInterpolationAutomatonBuilder {
	
	private ArrayList<IPredicate> m_StateSequence;
//	private final IPredicate[] m_Interpolants;
	private final NestedWordAutomaton<CodeBlock, IPredicate> m_IA;
	private final PredicateUnifier m_PredicateUnifier;
//	private final TraceChecker m_TraceChecker;
	private final INestedWordAutomaton<CodeBlock, IPredicate> m_Abstraction;
	
	private final SmtManager m_SmtManager;
	
	private final ArrayDeque<IPredicate> m_Worklist = new ArrayDeque<IPredicate>();
	private final Set<IPredicate> m_Annotated = new HashSet<IPredicate>();
	
//	private final IPredicate m_TruePredicate;
//	private final IPredicate m_FalsePredicate;
	private final AutomatonEpimorphism<IPredicate> m_Epimorphism;
	private final EdgeChecker m_EdgeChecker;
	private final ModifiableGlobalVariableManager m_ModifiedGlobals;
	private final INTERPOLATION m_Interpolation;
	public TotalInterpolationAutomatonBuilder(
			INestedWordAutomaton<CodeBlock, IPredicate> abstraction,
			ArrayList<IPredicate> stateSequence, TraceChecker traceChecker,
			SmtManager smtManager, PredicateFactory predicateFactory, 
			ModifiableGlobalVariableManager modifiableGlobals,
			INTERPOLATION interpolation) throws OperationCanceledException {
		super();
		m_StateSequence = stateSequence;
//		m_TraceChecker = traceChecker;
		m_SmtManager = smtManager;
//		m_Interpolants = traceChecker.getInterpolants();
		m_PredicateUnifier = traceChecker.getPredicateUnifier();
		m_Abstraction = abstraction;
		InCaReAlphabet<CodeBlock> alphabet = new InCaReAlphabet<CodeBlock>(abstraction);
		m_IA = (new StraightLineInterpolantAutomatonBuilder(
				alphabet , traceChecker, predicateFactory)).getResult();
		m_ModifiedGlobals = modifiableGlobals;
		m_Interpolation = interpolation;
		m_Epimorphism = new AutomatonEpimorphism<IPredicate>();
		{
			IPredicate firstAutomatonState = m_StateSequence.get(0); 
			m_Epimorphism.insert(firstAutomatonState, traceChecker.getPrecondition());
			m_Annotated.add(firstAutomatonState);
			m_Worklist.add(firstAutomatonState);
		}
		addInterpolants(m_StateSequence, traceChecker.getInterpolants());
		{
			IPredicate lastAutomatonState = m_StateSequence.get(m_StateSequence.size()-1); 
			m_Epimorphism.insert(lastAutomatonState, traceChecker.getPostcondition());
			m_Annotated.add(lastAutomatonState);
			m_Worklist.add(lastAutomatonState);
		}		
		m_EdgeChecker = new EdgeChecker(m_SmtManager, m_ModifiedGlobals);
		for (IPredicate state : stateSequence) {
			m_Worklist.add(state);
			m_Annotated.add(state);
		}
		while (!m_Worklist.isEmpty()) {
			IPredicate p = m_Worklist.removeFirst();
			doThings(p);
		}
	}
	
	
	private void doThings(IPredicate p) throws OperationCanceledException {
		for (OutgoingInternalTransition<CodeBlock, IPredicate> transition : 
			m_Abstraction.internalSuccessors(p)) {
			continueCheckForOutgoingPath(p, transition, transition.getSucc());
		}
		for (OutgoingCallTransition<CodeBlock, IPredicate> transition : 
			m_Abstraction.callSuccessors(p)) {
			continueCheckForOutgoingPath(p, transition, transition.getSucc());
		}
		for (OutgoingReturnTransition<CodeBlock, IPredicate> transition : 
			m_Abstraction.returnSuccessors(p)) {
			if (m_Annotated.contains(transition.getHierPred())) {
				continueCheckForOutgoingPath(p, transition, transition.getSucc());
			}
		}


	}


	private void continueCheckForOutgoingPath(IPredicate p,
			Transitionlet<CodeBlock, IPredicate> transition,
			IPredicate succ) throws OperationCanceledException {
		if (m_Annotated.contains(succ)) {
			IPredicate predItp = m_Epimorphism.getMapping(p);
			IPredicate succItp = m_Epimorphism.getMapping(succ);
			// this is a one-step path, no need to call TraceChecker
			if (interpolantAutomatonContainsTransition(predItp, transition, succItp)) {
				// do nothing, transition is already contained
			} else {
				checkRunOfLenthOne(predItp, transition, succItp);
			}
		} else {
			NestedRun<CodeBlock, IPredicate> runStartingInSucc = findRun(succ, m_Annotated);
			if (runStartingInSucc != null) {
				NestedRun<CodeBlock, IPredicate> firstStep = constructRunOfLengthOne(p, transition);
				NestedRun<CodeBlock, IPredicate> completeRun = firstStep.concatenate(runStartingInSucc);
				checkRun(completeRun);
			}
		}
		
	}
	
	private boolean interpolantAutomatonContainsTransition(IPredicate predItp,
			Transitionlet<CodeBlock, IPredicate> transition, IPredicate succItp) {
		if (transition instanceof OutgoingInternalTransition) {
			OutgoingInternalTransition<CodeBlock, IPredicate> internalTrans = 
					(OutgoingInternalTransition<CodeBlock, IPredicate>) transition;
			return m_IA.succInternal(predItp, internalTrans.getLetter()).contains(succItp);
		} else if (transition instanceof OutgoingCallTransition) {
			OutgoingCallTransition<CodeBlock, IPredicate> callTrans = 
					(OutgoingCallTransition<CodeBlock, IPredicate>) transition;
			return m_IA.succCall(predItp, callTrans.getLetter()).contains(succItp);
		} else if (transition instanceof OutgoingReturnTransition) {
			OutgoingReturnTransition<CodeBlock, IPredicate> returnTrans = 
					(OutgoingReturnTransition<CodeBlock, IPredicate>) transition;
			IPredicate hierPredItp = m_Epimorphism.getMapping(returnTrans.getHierPred());
			return m_IA.succReturn(predItp, hierPredItp, returnTrans.getLetter()).contains(succItp);
		} else if (transition instanceof SummaryReturnTransition) {
			SummaryReturnTransition<CodeBlock, IPredicate> summaryTrans = 
					(SummaryReturnTransition<CodeBlock, IPredicate>) transition;
			IPredicate linPredItp = m_Epimorphism.getMapping(summaryTrans.getLinPred());
			return m_IA.succReturn(linPredItp, predItp, summaryTrans.getLetter()).contains(succItp);
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}
	}
	
	private NestedRun<CodeBlock, IPredicate> constructRunOfLengthOne(IPredicate p,
			Transitionlet<CodeBlock, IPredicate> transition) {
		if (transition instanceof OutgoingInternalTransition) {
			OutgoingInternalTransition<CodeBlock, IPredicate> internalTrans = 
					(OutgoingInternalTransition<CodeBlock, IPredicate>) transition;
			return new NestedRun<>(p, internalTrans.getLetter(), NestedWord.INTERNAL_POSITION, internalTrans.getSucc());
		} else if (transition instanceof OutgoingCallTransition) {
			OutgoingCallTransition<CodeBlock, IPredicate> callTrans = 
					(OutgoingCallTransition<CodeBlock, IPredicate>) transition;
			return new NestedRun<>(p, callTrans.getLetter(), NestedWord.PLUS_INFINITY, callTrans.getSucc());
		} else if (transition instanceof OutgoingReturnTransition) {
			OutgoingReturnTransition<CodeBlock, IPredicate> returnTrans = 
					(OutgoingReturnTransition<CodeBlock, IPredicate>) transition;
			return new NestedRun<>(p, returnTrans.getLetter(), NestedWord.MINUS_INFINITY, returnTrans.getSucc());
		} else if (transition instanceof SummaryReturnTransition) {
			SummaryReturnTransition<CodeBlock, IPredicate> summaryTrans = 
					(SummaryReturnTransition<CodeBlock, IPredicate>) transition;
			return new NestedRun<>(summaryTrans.getLinPred(), summaryTrans.getLetter(), NestedWord.MINUS_INFINITY, summaryTrans.getSucc());
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}
		
	}


	private void checkRunOfLenthOne(IPredicate predItp,
			Transitionlet<CodeBlock, IPredicate> transition, IPredicate succItp) {
		assert m_EdgeChecker.isAssertionStackEmpty();
		m_EdgeChecker.assertCodeBlock(transition.getLetter());
		if (transition instanceof OutgoingInternalTransition) {
			OutgoingInternalTransition<CodeBlock, IPredicate> internalTrans = 
					(OutgoingInternalTransition<CodeBlock, IPredicate>) transition;
			m_EdgeChecker.assertPrecondition(predItp);
			LBool lbool = m_EdgeChecker.postInternalImplies(succItp);
			if (lbool == LBool.UNSAT) {
				m_IA.addInternalTransition(predItp, internalTrans.getLetter(), succItp);
			}
		} else if (transition instanceof OutgoingCallTransition) {
			OutgoingCallTransition<CodeBlock, IPredicate> callTrans = 
					(OutgoingCallTransition<CodeBlock, IPredicate>) transition;
			m_EdgeChecker.assertPrecondition(predItp);
			LBool lbool = m_EdgeChecker.postCallImplies(succItp);
			if (lbool == LBool.UNSAT) {
				m_IA.addCallTransition(predItp, callTrans.getLetter(), succItp);
			}
		} else if (transition instanceof OutgoingReturnTransition) {
			OutgoingReturnTransition<CodeBlock, IPredicate> returnTrans = 
					(OutgoingReturnTransition<CodeBlock, IPredicate>) transition;
			IPredicate hierPredItp = m_Epimorphism.getMapping(returnTrans.getHierPred());
			m_EdgeChecker.assertPrecondition(predItp);
			m_EdgeChecker.assertHierPred(hierPredItp);
			LBool lbool = m_EdgeChecker.postReturnImplies(succItp);
			if (lbool == LBool.UNSAT) {
				m_IA.addReturnTransition(predItp, hierPredItp, returnTrans.getLetter(), succItp);
			}
			m_EdgeChecker.unAssertHierPred();
		} else if (transition instanceof SummaryReturnTransition) {
			SummaryReturnTransition<CodeBlock, IPredicate> summaryTrans = 
					(SummaryReturnTransition<CodeBlock, IPredicate>) transition;
			IPredicate linPredItp = m_Epimorphism.getMapping(summaryTrans.getLinPred());
			m_EdgeChecker.assertPrecondition(linPredItp);
			m_EdgeChecker.assertHierPred(predItp);
			LBool lbool = m_EdgeChecker.postReturnImplies(succItp);
			if (lbool == LBool.UNSAT) {
				m_IA.addReturnTransition(linPredItp, predItp, summaryTrans.getLetter(), succItp);
			}
			m_EdgeChecker.unAssertHierPred();
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}
		m_EdgeChecker.unAssertPrecondition();
		m_EdgeChecker.unAssertCodeBlock();
	}
	
	private void caseDistinction(IPredicate p,
			Transitionlet<CodeBlock, IPredicate> transition, IPredicate succ) {
		if (transition instanceof OutgoingInternalTransition) {
			OutgoingInternalTransition<CodeBlock, IPredicate> internalTrans = 
					(OutgoingInternalTransition<CodeBlock, IPredicate>) transition;
		} else if (transition instanceof OutgoingCallTransition) {
			OutgoingCallTransition<CodeBlock, IPredicate> callTrans = 
					(OutgoingCallTransition<CodeBlock, IPredicate>) transition;
		} else if (transition instanceof OutgoingReturnTransition) {
			OutgoingReturnTransition<CodeBlock, IPredicate> returnTrans = 
					(OutgoingReturnTransition<CodeBlock, IPredicate>) transition;
		} else if (transition instanceof SummaryReturnTransition) {
			SummaryReturnTransition<CodeBlock, IPredicate> summaryTrans = 
					(SummaryReturnTransition<CodeBlock, IPredicate>) transition;
		} else {
			throw new AssertionError("unsupported" + transition.getClass());
		}
		
	}


	private void checkRun(NestedRun<CodeBlock, IPredicate> run) {
		IPredicate first = run.getStateAtPosition(0);
		IPredicate last = run.getStateAtPosition(run.getLength()-1);
		IPredicate precondition = m_Epimorphism.getMapping(first);
		IPredicate postcondition = m_Epimorphism.getMapping(last);
		SortedMap<Integer, IPredicate> pendingContexts = computePendingContexts(run);
//		SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<>();
		TraceChecker tc = new TraceChecker(precondition, postcondition, 
				pendingContexts , run.getWord(), m_SmtManager, m_ModifiedGlobals);
		if (tc.isCorrect() == LBool.UNSAT) {
			tc.computeInterpolants(new TraceChecker.AllIntegers(), m_PredicateUnifier, m_Interpolation);
			addInterpolants(run.getStateSequence(), tc.getInterpolants());
			addTransitions(run.getStateSequence(), tc);
		} else {
			tc.finishTraceCheckWithoutInterpolantsOrProgramExecution();
		}
	}


	private SortedMap<Integer, IPredicate> computePendingContexts(
			NestedRun<CodeBlock, IPredicate> run) {
		SortedMap<Integer, IPredicate> result = new TreeMap<>();
		for (int pendingReturnPos : run.getWord().getPendingReturns().keySet()) {
			IPredicate linPred = run.getStateAtPosition(pendingReturnPos);
			Iterable<IPredicate> hierPreds = m_Abstraction.hierPred(linPred, run.getSymbol(pendingReturnPos));
			IPredicate hierPred = getSomeAnnotatedState(hierPreds);
			if (hierPred == null) {
				throw new AssertionError("found nothing");
			} else {
				result.put(pendingReturnPos, m_Epimorphism.getMapping(hierPred));
			}
		}
		return result;
	}


	private IPredicate getSomeAnnotatedState(Iterable<IPredicate> states) {
		for (IPredicate state : states) {
			if (m_Annotated.contains(state)) {
				return state;
			}
		}
		return null;
	}


	private void addTransitions(ArrayList<IPredicate> stateSequence,
			TraceChecker tc) {
		InterpolantsPreconditionPostcondition ipp = new InterpolantsPreconditionPostcondition(tc);
		NestedWord<CodeBlock> nw = NestedWord.nestedWord(tc.getTrace());
		for (int i=0; i<nw.length(); i++) {
			if (nw.isInternalPosition(i)) {
				m_IA.addInternalTransition(ipp.getInterpolant(i), nw.getSymbol(i), ipp.getInterpolant(i+1));
			} else if (nw.isCallPosition(i)) {
				m_IA.addCallTransition(ipp.getInterpolant(i), nw.getSymbol(i), ipp.getInterpolant(i+1));
			} else if (nw.isReturnPosition(i)) {
				IPredicate hierPred;
				if (nw.isPendingReturn(i)) {
					hierPred = tc.getPendingContexts().get(i);
				} else {
					int callPredPos = nw.getCallPosition(i);
					hierPred = ipp.getInterpolant(callPredPos);
				}
				m_IA.addReturnTransition(ipp.getInterpolant(i), hierPred, nw.getSymbol(i), ipp.getInterpolant(i+1));
			} else {
				throw new AssertionError();
			}
		}
	}


	private void addInterpolants(ArrayList<IPredicate> stateSequence,
			IPredicate[] interpolants) {
		for (int i=0; i<interpolants.length; i++) {
			IPredicate state = stateSequence.get(i + 1);
			IPredicate interpolant = interpolants[i];
			if (!m_IA.getStates().contains(interpolant)) {
				m_IA.addState(false, false, interpolant);
			}
			m_Annotated.add(state);
			m_Epimorphism.insert(state, interpolant);
			m_Worklist.add(state);
		}
	}


	private NestedRun<CodeBlock, IPredicate> findRun(IPredicate p,
			Set<IPredicate> annotated) throws OperationCanceledException {
		return (new IsEmpty<CodeBlock, IPredicate>(m_Abstraction, Collections.singleton(p), m_Annotated)).getNestedRun();
	}


	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return m_IA;
	}
	
	


//	private void startDfs(IPredicate state,
//			OutgoingInternalTransition<CodeBlock, IPredicate> transition) {
//		new GraphDfs(null, state, transition);
//	}
//
//
//	private class GraphDfs {
//		private final Set<IPredicate> m_Goal;
//		private final Set<IPredicate> m_Visited = new HashSet<IPredicate>();
//		private final Stack<Iterator<?>> m_IteratorStack = new Stack<Iterator<?>>();
//		private final Stack<Transitionlet<CodeBlock, IPredicate>> m_TransitionStack = new Stack<Transitionlet<CodeBlock, IPredicate>>();
//		private final Stack<IPredicate> m_StateStack = new Stack<IPredicate>();
//		private final Stack<IPredicate> m_CallPredecessors = new Stack<IPredicate>();
//		
//		IPredicate m_CurrentPred;
//		IPredicate m_CurrentSucc;
//		Iterator<Transitionlet<CodeBlock, IPredicate>> m_CurrentIterator;
//		Transitionlet<CodeBlock, IPredicate> m_CurrentTransition;
//		
//		
//		
//		public GraphDfs(Set<IPredicate> goal, IPredicate currentPred,
//				Transitionlet<CodeBlock, IPredicate> initialTransition) {
//			super();
//			m_Goal = goal;
//			m_CurrentPred = currentPred;
//			m_CurrentTransition = initialTransition;
//			m_CurrentIterator = null;
//			m_CurrentSucc = getSuccessor(initialTransition);
//		}
//		
//		private IPredicate getSuccessor(Transitionlet<CodeBlock, IPredicate> transition) {
//			IPredicate result;
//			if (transition instanceof OutgoingInternalTransition) {
//				result = ((OutgoingInternalTransition<CodeBlock, IPredicate>) transition).getSucc();
//			} else if (transition instanceof OutgoingCallTransition) {
//				result = ((OutgoingCallTransition<CodeBlock, IPredicate>) transition).getSucc();
//			} else if (transition instanceof OutgoingReturnTransition) {
//				result = ((OutgoingReturnTransition<CodeBlock, IPredicate>) transition).getSucc();
//			} else {
//				throw new AssertionError("unsupported" + transition.getClass());
//			}
//			return result;
//		}
//
//		public void searchGoal() {
//			while (!m_Goal.contains(m_CurrentSucc)) {
//				m_Visited.add(m_CurrentSucc);
//				push();
//				getNextTransition();
//				while(m_CurrentTransition == null) {
//					if (getStackHeight() == 1) {
//						// we never iterate over the initial Iterator.
//						return;
//					}
//					pop();
//					getNextTransition();
//				}
//				m_CurrentSucc = getSuccessor(m_CurrentTransition);
//			}
//		}
//		
//		private int getStackHeight() {
//			assert allStacksHaveSameHeight();
//			return m_StateStack.size();
//		}
//		
//		private boolean allStacksHaveSameHeight() {
//			boolean result = (m_StateStack.size() == m_IteratorStack.size());
//			result &= (m_StateStack.size() == m_TransitionStack.size());
//			return result;
//		}
//		
//		private void push() {
//			assert allStacksHaveSameHeight();
//			m_TransitionStack.push(m_CurrentTransition);
//			m_IteratorStack.push(m_CurrentIterator);
//			m_StateStack.push(m_CurrentPred);
//			if (m_CurrentTransition instanceof OutgoingCallTransition) {
//				m_CallPredecessors.add(m_CurrentPred);
//			}
//			m_CurrentPred = m_CurrentSucc;
//			m_CurrentTransition = null;
//			m_CurrentIterator = null;
//			m_CurrentSucc = null;
//		}
//		
//		private void pop() {
//			assert allStacksHaveSameHeight();
//			m_CurrentSucc = m_CurrentPred;
//			m_CurrentPred = m_StateStack.pop();
//			if (m_CurrentTransition instanceof OutgoingCallTransition) {
//				IPredicate callPred = m_CallPredecessors.pop();
//				assert callPred == m_CurrentPred;
//			}
//			m_CurrentIterator = (Iterator<Transitionlet<CodeBlock, IPredicate>>) m_IteratorStack.pop();
//			m_CurrentTransition = m_TransitionStack.pop();
//		}
//		
//		public void getNextTransition() {
//			if (m_CurrentIterator.hasNext()) {
//				m_CurrentTransition = m_CurrentIterator.next();
//			} else {
//				if (m_CurrentTransition instanceof OutgoingInternalTransition) {
//					switchIteratorInternalToCall();
//					//TODO: implement
//				}
//			}
//			if (m_CurrentTransition instanceof OutgoingInternalTransition) {
//				m_CurrentTransition = getNextInternalTransition();
//				if (m_CurrentTransition == null) {
//					
//				}
//			}
//			
//		}
//		
//		public void switchIteratorInternalToCall() {
//			assert !m_IteratorStack.peek().hasNext();
//			m_IteratorStack.pop();
//			IPredicate top = m_StateStack.peek();
//			Iterator<OutgoingCallTransition<CodeBlock, IPredicate>> it = m_Abstraction.callSuccessors(top).iterator();
//			m_IteratorStack.push(it);
//		}
//		
//		public void switchIteratorCallToReturn() {
//			assert !m_IteratorStack.peek().hasNext();
//			m_IteratorStack.pop();
//			IPredicate top = m_StateStack.peek();
//			Iterator<OutgoingReturnTransition<CodeBlock, IPredicate>> it = m_Abstraction.returnSuccessors(top).iterator();
//			m_IteratorStack.push(it);
//		}
//		
//		public OutgoingInternalTransition<CodeBlock, IPredicate> getNextInternalTransition() {
//			if (m_IteratorStack.peek().hasNext()) {
//				return (OutgoingInternalTransition<CodeBlock, IPredicate>) m_IteratorStack.peek().next();
//			} else {
//				return null;
//			}
//		}
//	}
//	

}
