package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.NestedLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates.StronglyConnectedComponents.SCC;

class LassoConstructor<LETTER, STATE> {
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Nwars;
    private final StateContainer<LETTER,STATE> m_Goal;
    private final Set<StateContainer<LETTER,STATE>> m_Visited =
                    new HashSet<StateContainer<LETTER,STATE>>();
    private final ArrayList<Map<StateContainer<LETTER,STATE>,SuccessorInfo>> m_SuccInfos = 
    		new ArrayList<Map<StateContainer<LETTER,STATE>,SuccessorInfo>>();
    private final SCC m_Scc;
    private final boolean m_FindAcceptingSummary;
    private int m_Iteration;
    private boolean m_GoalFound = false;
    private NestedRun<LETTER, STATE> m_Loop;
    private NestedRun<LETTER, STATE> m_Stem;
    private NestedLassoRun<LETTER, STATE> m_Lasso;
    
	public LassoConstructor(
			NestedWordAutomatonReachableStates<LETTER, STATE> nwars, 
			StateContainer<LETTER, STATE> goal, SCC scc) {
		m_Nwars = nwars;
		m_Goal = goal;
		m_Scc = scc;
		m_FindAcceptingSummary = false;
		//first, find a run, while doing a backward breadth first search
		{
			m_Iteration = 0;
			Map<StateContainer<LETTER, STATE>, SuccessorInfo> map = 
					new HashMap<StateContainer<LETTER,STATE>,SuccessorInfo>();
			m_SuccInfos.add(map);
			addPredecessors(m_Goal, map);
		}
		findRunBackwards();
		constructRunOfLoop();
		m_Stem = (new RunConstructor<LETTER, STATE>(m_Nwars, m_Goal, null, false)).constructRun();
		m_Lasso = new NestedLassoRun<LETTER, STATE>(m_Stem, m_Loop);
	}
	
	public LassoConstructor(
			NestedWordAutomatonReachableStates<LETTER, STATE> nwars, 
			Summary<LETTER, STATE> summary, SCC scc) {
		m_Nwars = nwars;
		m_Goal = summary.getSucc();
		m_Scc = scc;
		m_FindAcceptingSummary = true;
		//first, find a run, while doing a backward breadth first search
		{
			m_Iteration = 0;
			Map<StateContainer<LETTER, STATE>, SuccessorInfo> map = 
					new HashMap<StateContainer<LETTER,STATE>,SuccessorInfo>();
			m_SuccInfos.add(map);
			SuccessorInfo succInfo = new SuccessorInfo(
					summary.obtainIncomingReturnTransition(m_Nwars), m_Goal);
			map.put(summary.getHierPred(), succInfo);
//			addPredecessors(m_Goal, map);
		}
		findRunBackwards();
		constructRunOfLoop();
		m_Stem = (new RunConstructor<LETTER, STATE>(m_Nwars, m_Goal, null, false)).constructRun();
		m_Lasso = new NestedLassoRun<LETTER, STATE>(m_Stem, m_Loop);
	}

	
	/**
	 * Check iteratively precedessors and add SuccInfos to m_SuccInfos
	 */
	private void findRunBackwards() {
		while (!m_GoalFound) {
			if (m_Iteration > m_Scc.getNumberOfStates()) {
				throw new AssertionError("unable to find state in SCC");
			}
			assert m_SuccInfos.size() == m_Iteration + 1;
			m_Iteration++;
			Map<StateContainer<LETTER, STATE>, SuccessorInfo> map = 
					new HashMap<StateContainer<LETTER,STATE>,SuccessorInfo>();
			m_SuccInfos.add(map);
			for (StateContainer<LETTER, STATE> sc  : m_SuccInfos.get(m_Iteration-1).keySet()) {
				addPredecessors(sc, map);
			}
		}
	}

	/**
	 * Use m_SuccInfos to construct a run for a loop that has been found.
	 */
	private void constructRunOfLoop() {
		//then we reconstruct the run
		m_Loop = new NestedRun<LETTER, STATE>(m_Goal.getState());
		StateContainer<LETTER, STATE> current = m_Goal;
		for (int i=m_Iteration; i>=0; i--) {
			NestedRun<LETTER, STATE> newSuffix;
			SuccessorInfo info = m_SuccInfos.get(i).get(current);
			if (info.getTransition() instanceof IncomingInternalTransition) {
				IncomingInternalTransition<LETTER, STATE> inTrans = (IncomingInternalTransition<LETTER, STATE>) info.getTransition();
				newSuffix = new NestedRun<LETTER, STATE>(current.getState(), inTrans.getLetter(), NestedWord.INTERNAL_POSITION, info.getSuccessor().getState());
			} else if (info.getTransition() instanceof IncomingCallTransition) {
				IncomingCallTransition<LETTER, STATE> inTrans = (IncomingCallTransition<LETTER, STATE>) info.getTransition();
				newSuffix = new NestedRun<LETTER, STATE>(current.getState(), inTrans.getLetter(), NestedWord.PLUS_INFINITY, info.getSuccessor().getState());
			} else if (info.getTransition() instanceof IncomingReturnTransition) {
				IncomingReturnTransition<LETTER, STATE> inTrans = (IncomingReturnTransition<LETTER, STATE>) info.getTransition();
				StateContainer<LETTER, STATE> returnPredSc = m_Nwars.obtainSC(inTrans.getLinPred());
				boolean summaryMustContainAccepting = m_FindAcceptingSummary && i == 0;
				NestedRun<LETTER, STATE> summaryPrefix = (new RunConstructor<LETTER, STATE>(m_Nwars, returnPredSc, current, summaryMustContainAccepting)).constructRun();
				assert summaryPrefix != null : "no run for summary found";
				NestedRun<LETTER, STATE> returnSuffix = 
					new NestedRun<LETTER, STATE>(inTrans.getLinPred(), 
								inTrans.getLetter(), 
								NestedWord.MINUS_INFINITY, info.getSuccessor().getState());
				NestedRun<LETTER, STATE> summaryRun = summaryPrefix.concatenate(returnSuffix);
				newSuffix = summaryRun;
				
			} else {
				throw new AssertionError("unsupported transition");
			}
			m_Loop = m_Loop.concatenate(newSuffix);
			current = info.getSuccessor();
		}
	}
    
    public NestedLassoRun<LETTER, STATE> getNestedLassoRun() {
		return m_Lasso;
	}

    /**
     * Add for all predecessors of sc that have not yet been visited the
     * successor information to map.
     */
	private void addPredecessors(StateContainer<LETTER,STATE> sc, Map<StateContainer<LETTER,STATE>,SuccessorInfo> succInfo) {
		for (IncomingReturnTransition<LETTER, STATE> inTrans : m_Nwars.returnPredecessors(sc.getState())) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getHierPred());
			checkAndAddPredecessor(sc, succInfo, inTrans, predSc);
		}
		for (IncomingCallTransition<LETTER, STATE> inTrans : m_Nwars.callPredecessors(sc.getState())) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
			checkAndAddPredecessor(sc, succInfo, inTrans, predSc);
		}
		for (IncomingInternalTransition<LETTER, STATE> inTrans : m_Nwars.internalPredecessors(sc.getState())) {
			StateContainer<LETTER, STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
			checkAndAddPredecessor(sc, succInfo, inTrans, predSc);
		}
    }

	/**
	 * Add successor information for predSc and inTrans, if predSc is in
	 * SCC and has not been visited before.
	 */
	private void checkAndAddPredecessor(StateContainer<LETTER, STATE> sc,
			Map<StateContainer<LETTER, STATE>, SuccessorInfo> succInfo,
			Transitionlet<LETTER, STATE> inTrans,
			StateContainer<LETTER, STATE> predSc) {
		if (m_Scc.getAllStates().contains(predSc) && !m_Visited.contains(predSc)) {
			m_Visited.add(predSc);
			SuccessorInfo info = new SuccessorInfo(inTrans, sc);
			succInfo.put(predSc, info);
			if (m_Goal.equals(predSc)) {
				m_GoalFound = true;
			}
		}
	}
	
	
	
	private class SuccessorInfo {
		private final Transitionlet<LETTER, STATE> m_Transition;
		private final StateContainer<LETTER,STATE> m_Successor;
		public SuccessorInfo(Transitionlet<LETTER, STATE> transition, StateContainer<LETTER, STATE> successor) {
			super();
			m_Transition = transition;
			m_Successor = successor;
		}
		public Transitionlet<LETTER, STATE> getTransition() {
			return m_Transition;
		}
		public StateContainer<LETTER, STATE> getSuccessor() {
			return m_Successor;
		}
		
	}
}