/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.SortedMap;
import java.util.Stack;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.StateContainer.DownStateProp;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;

/**
 * Construction of initial runs and runs for summaries. Runs are constructed
 * backwards, therefore m_Start is the last state in the run and m_Goal is
 * the first state of the run. 
 *
 */
class RunConstructor<LETTER,STATE> {
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Nwars;
	private final StateContainer<LETTER,STATE> m_Start;
	/**
	 * If goal is a down state of start we construct a run whose first state
	 * is goal and whose last state is start. If goal is null we construct
	 * an initial run whose last state is start.
	 */
	private final StateContainer<LETTER,STATE> m_Goal;
	private final Set<SummaryWithObligation> m_ForbiddenSummaries;
	private final boolean m_FindSummary;
	private final Summary<LETTER,STATE> m_Summary;
	private final boolean m_SummaryMustContainAccepting;
	private boolean m_GoalFound = false;
	private final Set<StateContainerWithObligation> m_Visited =
			new HashSet<StateContainerWithObligation>();
	
	/**
	 * Construction of an initial run whose last state is start.
	 */
	public RunConstructor(NestedWordAutomatonReachableStates<LETTER, STATE> nwars,
			StateContainer<LETTER, STATE> start) {
		m_Nwars = nwars;
		m_Start = start;
		m_Goal = null;
		m_ForbiddenSummaries = Collections.emptySet();
		m_FindSummary = false;
		m_Summary = null;
		m_SummaryMustContainAccepting = false;
	}
	
	
	/**
	 * Construction of run whose last state is start. The state goal can be
	 * either a down state of start or null.
	 * If goal is a down state of start we construct a run whose first state
	 * is goal and whose last state is start. If goal is null we construct
	 * an initial run whose last state is start.
	 */
	public RunConstructor(NestedWordAutomatonReachableStates<LETTER, STATE> nwars,
			Summary<LETTER,STATE> summary,
			boolean summaryMustContainAccepting) {
		m_Nwars = nwars;
		m_Start = summary.getLinPred();
		m_Goal = summary.getHierPred();
		m_FindSummary = true;
		m_Summary = summary;
		m_SummaryMustContainAccepting = summaryMustContainAccepting;
		SummaryWithObligation summaryWithObligation = 
				new SummaryWithObligation(m_Summary, m_SummaryMustContainAccepting);
		m_ForbiddenSummaries = Collections.singleton(summaryWithObligation);
	}
	
	/**
	 * Run construction for a summary where we may not take any summary in 
	 * forbiddenSummaries. This avoids endless loop in recursive calls (if there
	 * is a run that takes a summary twice, then there is a run that takes the 
	 * summary once).
	 */
	private RunConstructor(NestedWordAutomatonReachableStates<LETTER, STATE> nwars,
			Summary<LETTER,STATE> summary,
			boolean summaryMustContainAccepting,
			Set<SummaryWithObligation> forbiddenSummaries) {
		m_Nwars = nwars;
		m_Start = summary.getLinPred();
		m_Goal = summary.getHierPred();
		m_FindSummary = true;
		m_Summary = summary;
		m_SummaryMustContainAccepting = summaryMustContainAccepting;
		SummaryWithObligation summaryWithObligation = 
				new SummaryWithObligation(m_Summary, m_SummaryMustContainAccepting);
		m_ForbiddenSummaries = new HashSet<SummaryWithObligation>(forbiddenSummaries);
		m_ForbiddenSummaries.add(summaryWithObligation);
	}
	

	/**
	 * Find suitable predecessor in run construction. Returns incoming
	 * transition from the state with the lowest serial number (that has
	 * not been visited before).
	 */
	private Collection<TransitionWithObligation> findSuitablePredecessors(StateContainerWithObligation current) {
		SortedMap<Integer, Object> number2transition = new TreeMap<Integer, Object>(); 
		for (IncomingInternalTransition<LETTER, STATE> inTrans : m_Nwars.internalPredecessors(current.getObject().getState())) {
			if (!m_FindSummary && m_Nwars.isInitial(inTrans.getPred())) {
				m_GoalFound = true;
				return Collections.singleton(new TransitionWithObligation((Transitionlet<LETTER,STATE>) inTrans, false));
			}
			StateContainer<LETTER,STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
			if (m_FindSummary && !predSc.getDownStates().containsKey(m_Goal.getState())) {
				continue;
			}
			final boolean predObligation = current.hasObligation() && !m_Nwars.isFinal(predSc.getState());
			if (predObligation) {
				assert m_FindSummary;
				if (!predSc.hasDownProp(m_Goal.getState(), DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL)) {
					continue;
				}
			}
			StateContainerWithObligation predWithObligation = new StateContainerWithObligation(predSc, predObligation);
			if (m_Visited.contains(predWithObligation)) {
				continue;
			}
			int predSerialNumber = predSc.getSerialNumber();
			number2transition.put(predSerialNumber, 
					new TransitionWithObligation(inTrans, predObligation));
		}
		for (IncomingCallTransition<LETTER, STATE> inTrans : m_Nwars.callPredecessors(current.getObject().getState())) {
			StateContainer<LETTER,STATE> predSc = m_Nwars.obtainSC(inTrans.getPred());
			if (m_FindSummary) {
				if (m_Goal.equals(predSc) && !current.hasObligation()) {
					m_GoalFound = true;
					return Collections.singleton(new TransitionWithObligation((Transitionlet<LETTER,STATE>) inTrans, false));
				} else {
					continue;
				}
			} else {
				assert !current.hasObligation();
				if (m_Nwars.isInitial(inTrans.getPred())) {
					m_GoalFound = true;
					return Collections.singleton(new TransitionWithObligation((Transitionlet<LETTER,STATE>) inTrans, false));
				}
				StateContainerWithObligation predWithObligation = new StateContainerWithObligation(predSc, false);
				if (m_Visited.contains(predWithObligation)) {
					continue;
				}
				int predSerialNumber = predSc.getSerialNumber();
				if (!number2transition.containsKey(predSerialNumber)) {
					number2transition.put(predSerialNumber, 
							new TransitionWithObligation(inTrans, false));
				}
			}
		}
		
		for (IncomingReturnTransition<LETTER, STATE> inTrans : m_Nwars.returnPredecessors(current.getObject().getState())) {
			Summary<LETTER, STATE> summary = new Summary<LETTER, STATE>(
					m_Nwars.obtainSC(inTrans.getHierPred()), 
					m_Nwars.obtainSC(inTrans.getLinPred()),
					inTrans.getLetter(), current.getObject());
			if (!m_FindSummary && m_Nwars.isInitial(inTrans.getHierPred())) {
				m_GoalFound = true;
				return Collections.singleton(new TransitionWithObligation((Transitionlet<LETTER,STATE>) inTrans, false));
			}
			StateContainer<LETTER,STATE> predSc = m_Nwars.obtainSC(inTrans.getHierPred());
			if (m_FindSummary && !predSc.getDownStates().containsKey(m_Goal.getState())) {
				continue;
			}
			final boolean summaryWillSatisfyObligation;
			{
				boolean doWeWantToTakeAcceptingSummary = current.hasObligation() 
						&& !m_Nwars.isFinal(predSc.getState()) 
						&& m_Nwars.isAccepting(summary);
				if (doWeWantToTakeAcceptingSummary) {
					SummaryWithObligation swo = new SummaryWithObligation(summary, true);
					boolean areWeAllowedToTakeAcceptingSummary = !m_ForbiddenSummaries.contains(swo);
					if (areWeAllowedToTakeAcceptingSummary) {
						summaryWillSatisfyObligation = true;
					} else {
						summaryWillSatisfyObligation = false;
					}
				} else {
					summaryWillSatisfyObligation = false;
				}
			}
			SummaryWithObligation summaryWithSatifiedObligation = 
					new SummaryWithObligation(summary, false);
			if (summaryWillSatisfyObligation) {
				assert !m_ForbiddenSummaries.contains(summaryWithSatifiedObligation);
			} else {
				if (m_ForbiddenSummaries.contains(summaryWithSatifiedObligation)) {
					continue;
				}
			}
			final boolean predObligation = current.hasObligation() && 
					!m_Nwars.isFinal(predSc.getState()) && !summaryWillSatisfyObligation;
			if (predObligation) {
				assert m_FindSummary;
				if (!predSc.hasDownProp(m_Goal.getState(), DownStateProp.REACHABLE_FROM_FINAL_WITHOUT_CALL)) {
					continue;
				}
			}
			StateContainerWithObligation predWithObligation = new StateContainerWithObligation(predSc, predObligation);
			if (m_Visited.contains(predWithObligation)) {
				continue;
			}
			int predSerialNumber = predSc.getSerialNumber();
			Object previousEntry = number2transition.get(predSerialNumber);
			if (previousEntry instanceof RunConstructor.TransitionWithObligation) {
				// do nothing
			} else {
				assert previousEntry == null || (previousEntry instanceof SortedMap);
				SortedMap<Integer, TransitionWithObligation> linPredSerial2inTrans;
				if (previousEntry == null) {
					linPredSerial2inTrans = new TreeMap<Integer, TransitionWithObligation>();
					number2transition.put(predSerialNumber, linPredSerial2inTrans);
				} else {
					linPredSerial2inTrans = (SortedMap<Integer, TransitionWithObligation>) previousEntry;
				}
				StateContainer<LETTER, STATE> linPredSc = m_Nwars.obtainSC(inTrans.getLinPred());
				int linPredSerial = linPredSc.getSerialNumber();
				linPredSerial2inTrans.put(linPredSerial, 
						new TransitionWithObligation(inTrans, predObligation));
			}
		}
		ArrayList<TransitionWithObligation> result = new ArrayList<TransitionWithObligation>();
		for (Object value : number2transition.values()) {
			if (value instanceof RunConstructor.TransitionWithObligation) {
				TransitionWithObligation two = (TransitionWithObligation) value;
				assert two.getObject() instanceof IncomingInternalTransition || two.getObject() instanceof IncomingCallTransition;
				result.add(two);
			} else {
				assert value instanceof SortedMap;
				SortedMap<Integer, TransitionWithObligation> linPredSerial2inTrans = 
						(SortedMap<Integer, TransitionWithObligation>) value;
				for (TransitionWithObligation ret : linPredSerial2inTrans.values()) {
					result.add(ret);
				}
			}
		}
		return result;
	}
	
	
	
	/**
	 * Returns run whose first state is m_Goal and whose last state is 
	 * m_Start.
	 * @throws OperationCanceledException 
	 */
	NestedRun<LETTER, STATE> constructRun() throws OperationCanceledException {
		//TODO: Check if this timeout check is responsible for problems.
		if (!NestedWordAutomata.getMonitor().continueProcessing()) {
			throw new OperationCanceledException();
		}
		assert !m_SummaryMustContainAccepting || m_Goal != null;
		if (!m_FindSummary && m_Nwars.isInitial(m_Start.getState())) {
			return new NestedRun<LETTER, STATE>(m_Start.getState());
		}
		boolean startStateHasObligation = m_SummaryMustContainAccepting && !m_Nwars.isFinal(m_Start.getState());
		StateContainerWithObligation startStateWithStartObligation = 
				new StateContainerWithObligation(m_Start, startStateHasObligation);
		StateContainerWithObligation current = startStateWithStartObligation;
		Stack<Iterator<TransitionWithObligation>> predStack = new Stack<Iterator<TransitionWithObligation>>();
		Stack<RunWithObligation> takenStack = new Stack<RunWithObligation>();
		
		// if this is set the last round
		boolean backtrack = false;
		while (true) {
			if (backtrack) {
				backtrack = false;
			} else {
				assert !m_Visited.contains(current);
				m_Visited.add(current);
				assert predStack.size() == takenStack.size();
				Collection<TransitionWithObligation> predecessors = findSuitablePredecessors(current);
				predStack.push(predecessors.iterator());
			}
			while (!predStack.peek().hasNext()) {
				predStack.pop();
				if (takenStack.isEmpty()) {
					// I am not able to find a run.
					// Maybe taking this summary was a bad decision.
					assert m_Goal != null;
					return null;
				}
				RunWithObligation wrongDescision = takenStack.pop();
				 StateContainerWithObligation sc = wrongDescision.getStateWithObligation();
				assert m_Visited.contains(sc);
				m_Visited.remove(sc);
				if (takenStack.isEmpty()) {
					current = startStateWithStartObligation;
				} else {
					 RunWithObligation currentPrefix = takenStack.peek();
					current = currentPrefix.getStateWithObligation();
				}
			}
			
			TransitionWithObligation transitionWOToLowest = predStack.peek().next();
			assert transitionWOToLowest != null;
			Transitionlet<LETTER, STATE> transitionToLowest = transitionWOToLowest.getObject();
			StateContainer<LETTER,STATE> predSc;
			NestedRun<LETTER,STATE> newPrefix;
			if (transitionToLowest instanceof IncomingInternalTransition) {
				IncomingInternalTransition<LETTER, STATE> inTrans = 
						(IncomingInternalTransition<LETTER, STATE>) transitionToLowest;
				predSc = m_Nwars.obtainSC(inTrans.getPred());
				newPrefix = new NestedRun<LETTER, STATE>(inTrans.getPred(), 
						inTrans.getLetter(), NestedWord.INTERNAL_POSITION,
						current.getObject().getState());
			} else if (transitionToLowest instanceof IncomingCallTransition) {
				IncomingCallTransition<LETTER, STATE> inTrans = 
						(IncomingCallTransition<LETTER, STATE>) transitionToLowest;
				predSc = m_Nwars.obtainSC(inTrans.getPred());
				newPrefix = new NestedRun<LETTER, STATE>(inTrans.getPred(), 
						inTrans.getLetter(), NestedWord.PLUS_INFINITY, 
						current.getObject().getState());
			} else if (transitionToLowest instanceof IncomingReturnTransition) {
				IncomingReturnTransition<LETTER, STATE> inTrans = 
						(IncomingReturnTransition<LETTER, STATE>) transitionToLowest;
				predSc = m_Nwars.obtainSC(inTrans.getHierPred());
				Summary<LETTER, STATE> summary = new Summary<LETTER, STATE>(
						predSc, 
						m_Nwars.obtainSC(inTrans.getLinPred()),
						inTrans.getLetter(), current.getObject());
				boolean isAcceptingSummaryRequired = 
						current.hasObligation() && 
						!transitionWOToLowest.hasObligation() && 
						!m_Nwars.isFinal(predSc.getState());
				assert !isAcceptingSummaryRequired || m_Nwars.isAccepting(summary);
				RunConstructor<LETTER,STATE> runConstuctor = new RunConstructor<LETTER,STATE>(
						m_Nwars,
						summary,
						isAcceptingSummaryRequired,
						m_ForbiddenSummaries);
				newPrefix = runConstuctor.constructRun();
				if (newPrefix == null) {
					// no summary found (because of forbidden summaries?)
					// we have to backtrack
					backtrack = true;
					continue;
				}
			} else {
				throw new AssertionError();
			}
			assert current.getObject().getState() == newPrefix.getStateAtPosition(newPrefix.getLength()-1);
			StateContainerWithObligation predWo = new StateContainerWithObligation(
					predSc, transitionWOToLowest.hasObligation());
			RunWithObligation newPrefixWO = new RunWithObligation(
					predWo.getObject(), predWo.hasObligation(), newPrefix);
			takenStack.push(newPrefixWO);
			if (m_GoalFound) {
				return constructResult(takenStack);
			}
			current = predWo;
		}
	}

	private NestedRun<LETTER, STATE> constructResult(Stack<RunWithObligation> stack) {
		Iterator<RunWithObligation> it = stack.iterator();
		NestedRun<LETTER, STATE> result = it.next().getNestedRun();
		while(it.hasNext()) {
			result = it.next().getNestedRun().concatenate(result);
		}
		assert m_Start.getState() == result.getStateAtPosition(result.getLength()-1);
		if (m_FindSummary) {
			NestedRun<LETTER, STATE> returnSuffix = new NestedRun<LETTER, STATE>(
					m_Summary.getLinPred().getState(), 
					m_Summary.getLetter(), NestedWord.MINUS_INFINITY, 
					m_Summary.getSucc().getState());
			result = result.concatenate(returnSuffix);
		}
		return result;
	}
	
	
	private class ObjectWithObligation<E> {
		private final E m_Object;
		private final boolean m_Flag;
		public ObjectWithObligation(
				E object, boolean flag) {
			super();
			m_Object = object;
			m_Flag = flag;
		}
		public E getObject() {
			return m_Object;
		}

		public boolean hasObligation() {
			return m_Flag;
		}
		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + (m_Flag ? 1231 : 1237);
			result = prime * result
					+ ((m_Object == null) ? 0 : m_Object.hashCode());
			return result;
		}
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof ObjectWithObligation)) {
				return false;
			}
			ObjectWithObligation<E> other = (ObjectWithObligation) obj;
			if (m_Flag != other.m_Flag)
				return false;
			if (m_Object == null) {
				if (other.m_Object != null)
					return false;
			} else if (!m_Object.equals(other.m_Object))
				return false;
			return true;
		}
		@Override
		public String toString() {
			return "ObjectWithObligation [m_Object=" + m_Object + ", m_Flag="
					+ m_Flag + "]";
		}
		
		
	}
	
	private class TransitionWithObligation extends ObjectWithObligation<Transitionlet<LETTER,STATE>> {
		public TransitionWithObligation(Transitionlet<LETTER, STATE> object, boolean flag) {
			super(object, flag);
		}
	}
	
	private class StateContainerWithObligation extends ObjectWithObligation<StateContainer<LETTER,STATE>> {
		public StateContainerWithObligation(StateContainer<LETTER, STATE> object, boolean flag) {
			super(object, flag);
		}
	}
	
	private class RunWithObligation extends StateContainerWithObligation {
		private final NestedRun<LETTER,STATE> m_NestedRun;
		public RunWithObligation(StateContainer<LETTER, STATE> object, boolean flag, NestedRun<LETTER,STATE> nestedRun) {
			super(object, flag);
			m_NestedRun = nestedRun;
		}
		public NestedRun<LETTER,STATE> getNestedRun() {
			return m_NestedRun;
		}
		public StateContainerWithObligation getStateWithObligation() {
			return new StateContainerWithObligation(getObject(), hasObligation());
		}
	}
	
	private class SummaryWithObligation extends ObjectWithObligation<Summary<LETTER,STATE>> {
		public SummaryWithObligation(Summary<LETTER, STATE> object, boolean flag) {
			super(object, flag);
		}
	}
	
}
