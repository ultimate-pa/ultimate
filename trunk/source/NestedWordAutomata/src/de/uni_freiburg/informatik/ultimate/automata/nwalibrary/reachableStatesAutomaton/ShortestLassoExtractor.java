package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiAccepts;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Computes an accepting nested lasso run for a given Honda state. Expects 
 * that the Honda state is contained in an accepting SCC. Nested Runs from 
 * the Honda to an initial state (stem) and from the Honda to the Honda are
 * computed backwards using StacksOfFlaggedStates. The boolean flag is true
 * iff on the path from this stack to the honda an accepting state was
 * visited.
 * 
 * This is slow, old and superseded by the class LassoConstructor.
 * Problem: we do a backward search and store information about visited stacks,
 * this seems to be too costly.
 * 
 * This class does not give us the shortest lasso, because the construction of
 * the stem is not optimal.
 * 
 */
class ShortestLassoExtractor<LETTER, STATE> {
	
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Nwars;
	
	List<Set<StackOfFlaggedStates>> m_Iterations = new ArrayList<Set<StackOfFlaggedStates>>();
	
	final StateContainer<LETTER, STATE> m_Goal;
	StateContainer<LETTER, STATE> m_FirstFoundInitialState;
	
	int m_GoalFoundIteration = -1;
	int m_InitFoundIteration = -1;
	
	NestedLassoRun<LETTER, STATE> m_nlr;
	NestedRun<LETTER, STATE> m_Stem;
	NestedRun<LETTER, STATE> m_Loop;
	NestedRun<LETTER, STATE> m_ConstructedNestedRun;
	
	public ShortestLassoExtractor(NestedWordAutomatonReachableStates<LETTER, STATE> nwars, StateContainer<LETTER, STATE> goal) {
		m_Nwars = nwars;
		m_Goal = goal;
		addInitialStack(goal);
		findPath(1);
		s_Logger.debug("Stem length: " + m_InitFoundIteration);
		s_Logger.debug("Loop length: " + m_GoalFoundIteration);
		constructStem();
		constructLoop();
		m_nlr = new NestedLassoRun<LETTER, STATE>(m_Stem, m_Loop);
		s_Logger.debug("Stem " + m_Stem);
		s_Logger.debug("Loop " + m_Loop);
		assert (new BuchiAccepts<LETTER, STATE>(nwars, m_nlr.getNestedLassoWord())).getResult();
	}

	private StackOfFlaggedStates addInitialStack(StateContainer<LETTER, STATE> goal) {
		StackOfFlaggedStates initialStack = new StackOfFlaggedStates(goal, false);
		Set<StackOfFlaggedStates> initialStacks = new HashSet<StackOfFlaggedStates>();
		initialStacks.add(initialStack);
		m_Iterations.add(initialStacks);
		return initialStack;
	}
	public NestedLassoRun<LETTER, STATE> getNestedLassoRun() {
		return m_nlr;
	}
	
	
	void findPath(final int startingIteration) {
		int i = startingIteration;
		while (m_GoalFoundIteration == -1 || m_InitFoundIteration == -1) {
			Set<StackOfFlaggedStates> currentStacks = m_Iterations.get(i-1);
			Set<StackOfFlaggedStates> preceedingStacks = new HashSet<StackOfFlaggedStates>();
			m_Iterations.add(preceedingStacks);
			for (StackOfFlaggedStates stack  : currentStacks) {
				addPreceedingStacks(i, preceedingStacks, stack);
			}
			i++;
		}
	}

	/**
	 * @param i
	 * @param preceedingStacks
	 * @param stack
	 */
	private void addPreceedingStacks(int i,
			Set<StackOfFlaggedStates> preceedingStacks,
			StackOfFlaggedStates stack) {
		StateContainer<LETTER, STATE> cont = stack.getTopmostState();
		for (IncomingInternalTransition<LETTER, STATE> inTrans : cont.internalPredecessors()) {
			StateContainer<LETTER, STATE> predCont = m_Nwars.obtainSC(inTrans.getPred());
			boolean finalOnPathToHonda = stack.getTopmostFlag() || m_Nwars.isFinal(inTrans.getPred());
			if (finalOnPathToHonda && stack.height() > 1 && !stack.getSecondTopmostFlag()) {
				continue;
			}
			StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, finalOnPathToHonda);
			preceedingStacks.add(predStack);
			checkIfGoalOrInitReached(i, predStack, predCont);
		}
		if (stack.height() == 1) {
			// call is pending
			for (IncomingCallTransition<LETTER, STATE> inTrans : cont.callPredecessors()) {
				StateContainer<LETTER, STATE> predCont = m_Nwars.obtainSC(inTrans.getPred());
				boolean finalOnPathToHonda = stack.getTopmostFlag() || m_Nwars.isFinal(inTrans.getPred());
				StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, finalOnPathToHonda);
				preceedingStacks.add(predStack);
				checkIfGoalOrInitReached(i, predStack, predCont);
			}
		} else {			
			for (IncomingCallTransition<LETTER, STATE> inTrans : cont.callPredecessors()) {
				StateContainer<LETTER, STATE> predCont = m_Nwars.obtainSC(inTrans.getPred());
				boolean finalOnPathToHonda = stack.getTopmostFlag() || m_Nwars.isFinal(inTrans.getPred());
				if (!stack.getSecondTopmostState().getState().equals(inTrans.getPred())) {
					// call predecessor does not match state on stack
					continue;
				}
				if (finalOnPathToHonda != stack.getSecondTopmostFlag() && !m_Nwars.isFinal(inTrans.getPred())) {
					// information about finalOnPathToHonda does not match
					continue;
				}
				StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, finalOnPathToHonda);
				preceedingStacks.add(predStack);
				checkIfGoalOrInitReached(i, predStack, predCont);
			}
		}

		// TODO: Optimization (you can ignore stacks like (q0,false)  (q0,false)  (q1,true)
		for (IncomingReturnTransition<LETTER, STATE> inTrans : cont.returnPredecessors()) {
			// note that goal or init can never be reached 
			// (backwards) with empty stack directly after return.
			int oldPreceedingStackSize = preceedingStacks.size();
			if (stack.getTopmostFlag()) {
				StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, true, true);
				preceedingStacks.add(predStack);
			} else {
				boolean linPredIsFinal = m_Nwars.isFinal(inTrans.getLinPred());
				{
					StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, true, linPredIsFinal);
					preceedingStacks.add(predStack);
				}
				if (!m_Nwars.isFinal(inTrans.getHierPred()) && !linPredIsFinal) {
					StackOfFlaggedStates predStack = new StackOfFlaggedStates(stack, inTrans, false, linPredIsFinal);
					preceedingStacks.add(predStack);
				}
			}
			assert oldPreceedingStackSize + 2 >= preceedingStacks.size();
		}
	}
	
	void constructStem() {
		assert m_ConstructedNestedRun == null;
		Set<StackOfFlaggedStates> initIteration = m_Iterations.get(m_InitFoundIteration);
		StackOfFlaggedStates stack = new StackOfFlaggedStates(m_FirstFoundInitialState, true);
		if (!initIteration.contains(stack)) { 
			stack = new StackOfFlaggedStates(m_FirstFoundInitialState, false);
		}

		assert initIteration.contains(stack);
		StateContainer<LETTER, STATE> cont = m_FirstFoundInitialState;
		m_ConstructedNestedRun = new NestedRun<LETTER, STATE>(cont.getState());
		for (int i = m_InitFoundIteration-1; i>=0; i--) {
			stack = getSuccessorStack(stack, m_Iterations.get(i));
		}
		m_Stem = m_ConstructedNestedRun;
		m_ConstructedNestedRun = null;
	}
	
	void constructLoop() {
		Set<StackOfFlaggedStates> hondaIteration = m_Iterations.get(m_GoalFoundIteration);
		StackOfFlaggedStates stack = new StackOfFlaggedStates(m_Goal, true);
		if (!hondaIteration.contains(stack)) {
			stack = new StackOfFlaggedStates(m_Goal, false);
		}
		assert hondaIteration.contains(stack);
		StateContainer<LETTER, STATE> cont = m_Goal;
		m_ConstructedNestedRun = new NestedRun<LETTER, STATE>(cont.getState());
		m_Loop = new NestedRun<LETTER, STATE>(cont.getState());
		for (int i = m_GoalFoundIteration-1; i>=0; i--) {
			stack = getSuccessorStack(stack, m_Iterations.get(i));
		}
		m_Loop = m_ConstructedNestedRun;
		m_ConstructedNestedRun = null;
	}

	
	StackOfFlaggedStates getSuccessorStack(StackOfFlaggedStates sofs, Set<StackOfFlaggedStates> succCandidates) {
		StateContainer<LETTER, STATE> cont = sofs.getTopmostState();
		if (sofs.getTopmostFlag()) {
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : cont.internalSuccessors()) {
				StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, true);
				if (succCandidates.contains(succStack)) {
					NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
							cont.getState(), outTrans.getLetter(), NestedWord.INTERNAL_POSITION, outTrans.getSucc());
					m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
					return succStack;
				}
			}
			for (OutgoingCallTransition<LETTER, STATE> outTrans : cont.callSuccessors()) {
				StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, true, false);
				if (succCandidates.contains(succStack)) {
					NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
							cont.getState(), outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
					m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
					return succStack;
				}
				if (sofs.height() == 1) {
					//check also for pending calls
					succStack = new StackOfFlaggedStates(sofs, outTrans, true, true);
					if (succCandidates.contains(succStack)) {
						NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
								cont.getState(), outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
						m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
						return succStack;
					}

				}
			}
			if (sofs.height() > 1) {
				for (OutgoingReturnTransition<LETTER, STATE> outTrans : cont.returnSuccessors()) {
					if (sofs.getSecondTopmostState().getState().equals(outTrans.getHierPred())) {
						StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, true);
						if (succCandidates.contains(succStack)) {
							NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
									cont.getState(), outTrans.getLetter(), NestedWord.MINUS_INFINITY, outTrans.getSucc());
							m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
							return succStack;
						}
					}
				}
			}
		}
		for (OutgoingInternalTransition<LETTER, STATE> outTrans : cont.internalSuccessors()) {
			StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, false);
			if (succCandidates.contains(succStack)) {
				NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
						cont.getState(), outTrans.getLetter(), NestedWord.INTERNAL_POSITION, outTrans.getSucc());
				m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
				return succStack;
			}
		}
		for (OutgoingCallTransition<LETTER, STATE> outTrans : cont.callSuccessors()) {
			StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, false, false);
			if (succCandidates.contains(succStack)) {
				NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
						cont.getState(), outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
				m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
				return succStack;
			}
			if (sofs.height() == 1) {
				//check also for pending calls
				succStack = new StackOfFlaggedStates(sofs, outTrans, false, true);
				if (succCandidates.contains(succStack)) {
					NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
							cont.getState(), outTrans.getLetter(), NestedWord.PLUS_INFINITY, outTrans.getSucc());
					m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
					return succStack;
				}

			}
		}
		if (sofs.height() > 1) {
			for (OutgoingReturnTransition<LETTER, STATE> outTrans : cont.returnSuccessors()) {
				if (sofs.getSecondTopmostState().getState().equals(outTrans.getHierPred())) {
					StackOfFlaggedStates succStack = new StackOfFlaggedStates(sofs, outTrans, false);
					if (succCandidates.contains(succStack)) {
						NestedRun<LETTER, STATE> runSegment = new NestedRun<LETTER, STATE>(
								cont.getState(), outTrans.getLetter(), NestedWord.MINUS_INFINITY, outTrans.getSucc());
						m_ConstructedNestedRun = m_ConstructedNestedRun.concatenate(runSegment);
						return succStack;
					}
				}
			}
		}
		throw new AssertionError("no corresponding state found");
	}


	/**
	 * @param i
	 * @param stack
	 * @param inTrans
	 * @param predCont
	 */
	private void checkIfGoalOrInitReached(int i,
			StackOfFlaggedStates stack,
			StateContainer<LETTER, STATE> predCont) {
		if (predCont == m_Goal && stack.hasOnlyTopmostElement() && 
				stack.getTopmostFlag() == true) {
			m_GoalFoundIteration = i;
		}
		if (m_FirstFoundInitialState == null && 
				m_Nwars.isInitial(predCont.getState()) && 
				stack.hasOnlyTopmostElement()) {
			m_InitFoundIteration = i;
			m_FirstFoundInitialState = predCont;
		}
	}
	
	
	class StackOfFlaggedStates {
		private final StateContainer<LETTER, STATE> m_TopmostState;
		private final boolean m_TopmostFlag;
		private final StateContainer<LETTER, STATE>[] m_StateStack;
		private final boolean[] m_FlagStack;
		
		public int height() {
			return m_StateStack.length + 1;
		}
		


		/**
		 * Returns true if there is only one element on the stack, i.e., if 
		 * the topmost element is the only element on the stack.
		 */
		public boolean hasOnlyTopmostElement() {
			return m_StateStack.length == 0;
		}
		
		public StateContainer<LETTER, STATE> getSecondTopmostState() {
			return m_StateStack[m_StateStack.length-1];
		}

		public StateContainer<LETTER, STATE> getTopmostState() {
			return m_TopmostState;
		}
		
		public boolean getSecondTopmostFlag() {
			return m_FlagStack[m_FlagStack.length-1];
		}

		public boolean getTopmostFlag() {
			return m_TopmostFlag;
		}
		
		@SuppressWarnings("unchecked")
		public StackOfFlaggedStates(StateContainer<LETTER, STATE> cont, boolean flag) {
			m_StateStack = new StateContainer[0];
			m_FlagStack = new boolean[0];
			m_TopmostState = cont;
			m_TopmostFlag = flag;
		}

		public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
				IncomingInternalTransition<LETTER, STATE> inTrans, boolean flag) {
			m_StateStack = sofs.m_StateStack;
			m_FlagStack = sofs.m_FlagStack;
			m_TopmostState = m_Nwars.obtainSC(inTrans.getPred());
			m_TopmostFlag = flag;
		}
		
		public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
				IncomingCallTransition<LETTER, STATE> inTrans, boolean flag) {
			if (sofs.m_StateStack.length == 0) {
				m_StateStack = sofs.m_StateStack;
				m_FlagStack = sofs.m_FlagStack;
				m_TopmostState = m_Nwars.obtainSC(inTrans.getPred());
				m_TopmostFlag = flag;
				
			} else {
				m_StateStack = Arrays.copyOf(sofs.m_StateStack, sofs.m_StateStack.length-1); 
				m_FlagStack = Arrays.copyOf(sofs.m_FlagStack, sofs.m_FlagStack.length-1);
				m_TopmostState = m_Nwars.obtainSC(inTrans.getPred());
				m_TopmostFlag = flag;
			}
		}
		
		public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
				IncomingReturnTransition<LETTER, STATE> inTrans, boolean hierFlag, boolean linFlag) {
				m_StateStack = Arrays.copyOf(sofs.m_StateStack, sofs.m_StateStack.length+1); 
				m_FlagStack = Arrays.copyOf(sofs.m_FlagStack, sofs.m_FlagStack.length+1);
				m_StateStack[m_StateStack.length-1] = m_Nwars.obtainSC(inTrans.getHierPred());
				m_FlagStack[m_StateStack.length-1] = hierFlag;
				m_TopmostState = m_Nwars.obtainSC(inTrans.getLinPred());
				m_TopmostFlag = linFlag;
		}

		
		public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
				OutgoingInternalTransition<LETTER, STATE> outTrans, boolean flag) {
			m_StateStack = sofs.m_StateStack;
			m_FlagStack = sofs.m_FlagStack;
			m_TopmostState = m_Nwars.obtainSC(outTrans.getSucc());
			m_TopmostFlag = flag;
		}
		
		public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
				OutgoingCallTransition<LETTER, STATE> outTrans, boolean flag, boolean isPending) {
			if (isPending) {
				m_StateStack = sofs.m_StateStack;
				m_FlagStack = sofs.m_FlagStack;
				m_TopmostState = m_Nwars.obtainSC(outTrans.getSucc());
				m_TopmostFlag = flag;
			} else {
				m_StateStack = Arrays.copyOf(sofs.m_StateStack, sofs.m_StateStack.length+1); 
				m_FlagStack = Arrays.copyOf(sofs.m_FlagStack, sofs.m_FlagStack.length+1);
				m_StateStack[m_StateStack.length-1] = sofs.m_TopmostState;
				m_FlagStack[m_StateStack.length-1] = sofs.m_TopmostFlag;
				m_TopmostState = m_Nwars.obtainSC(outTrans.getSucc());
				m_TopmostFlag = flag;
			}
		}
		
		public StackOfFlaggedStates(StackOfFlaggedStates sofs, 
				OutgoingReturnTransition<LETTER, STATE> outTrans, boolean flag) {
				m_StateStack = Arrays.copyOf(sofs.m_StateStack, sofs.m_StateStack.length-1); 
				m_FlagStack = Arrays.copyOf(sofs.m_FlagStack, sofs.m_FlagStack.length-1);
				m_TopmostState = m_Nwars.obtainSC(outTrans.getSucc());
				m_TopmostFlag = flag;
		}

		@Override
		public int hashCode() {
			int result = HashUtils.hashJenkins(((Boolean) m_TopmostFlag).hashCode(), m_TopmostState);
//			result = HashUtils.hashJenkins(result, m_FlagStack);
			result = HashUtils.hashJenkins(result, m_StateStack);
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			StackOfFlaggedStates other = (StackOfFlaggedStates) obj;
			if (!getOuterType().equals(other.getOuterType()))
				return false;
			if (!Arrays.equals(m_FlagStack, other.m_FlagStack))
				return false;
			if (!Arrays.equals(m_StateStack, other.m_StateStack))
				return false;
			if (m_TopmostFlag != other.m_TopmostFlag)
				return false;
			if (m_TopmostState == null) {
				if (other.m_TopmostState != null)
					return false;
			} else if (!m_TopmostState.equals(other.m_TopmostState))
				return false;
			return true;
		}

		private ShortestLassoExtractor getOuterType() {
			return ShortestLassoExtractor.this;
		}

		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			for (int i=0; i<m_StateStack.length; i++) {
				sb.append("(" + m_StateStack[i].getState() + "," + m_FlagStack[i] + ")  ");
			}
			sb.append("(" + m_TopmostState.getState() + "," + m_TopmostFlag + ")");
			return sb.toString();
		}
		
		
	}
}
