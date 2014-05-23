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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.Transitionlet;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a
 * SuperDifference can compute a NWA nwa_difference such that nwa_difference
 * accepts all words that are accepted by nwa_minuend but not by
 * Psi(nwa_subtrahend), i.e. L(nwa_difference) = L(nwa_minuend) \ L(
 * Psi(nwa_subtrahend) ), where Psi is a transformation of the automaton
 * nwa_subtrahend that is defined by an implementation of IStateDeterminizer.
 * 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 * @param <LETTER>
 *            Symbol. Type of the elements of the alphabet over which the
 *            automata are defined.
 * @param <STATE>
 *            Content. Type of the labels that are assigned to the states of
 *            automata. In many cases you want to use String as STATE and your
 *            states are labeled e.g. with "q0", "q1", ...
 */

public class SuperDifference<LETTER, STATE> implements IOperation<LETTER, STATE> 
{
	/* *** *** *** Fields *** *** *** */

	// For status output
	private static Logger s_Logger = UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	// Automatons
	private final INestedWordAutomaton<LETTER, STATE> m_Minuend;
	private final INestedWordAutomaton<LETTER, STATE> m_Subtrahend;
	private final AutomatonEpimorphism<STATE> m_Epimorphism;
	private final NestedWordAutomaton<LETTER, STATE> m_Result;
	private final STATE m_SinkState;
	private final HashMap<String, STATE> m_ContainedStatesHashMap;
	private final StateFactory<STATE> m_StateFactory;

	/* *** *** *** Functions *** *** *** */
	@Override
	public String operationName() 
	{
		return "superDifference";
	}

	@Override
	public String startMessage() 
	{
		return "Start " + operationName() + ". Minuend "
				+ m_Minuend.sizeInformation() + " Subtrahend "
				+ m_Subtrahend.sizeInformation();
	}

	@Override
	public String exitMessage() 
	{
		return "Finished " + operationName() + " Result "
				+ m_Result.sizeInformation();
	}

	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult()
			throws OperationCanceledException
	{
		return m_Result;
	}

	/**
	 * Computes the an automaton A' which is the over approximation of the
	 * difference of the two automatons minuend and subtrahend such that L(A')
	 * >= L(minuend) - L(subtrahend) and L(A') <= L(minuend) Therefore it needs
	 * an automaton epimorphism
	 * 
	 * @param minuend
	 *            the minuend
	 * @param subtrahend
	 *            the subtrahend
	 * @param automatonEpimorhpism
	 *            the automaton epimorphism
	 * @param minimize
	 *            if true, the resulting automaton will be reduced
	 * @throws OperationCanceledException
	 */
	public SuperDifference(
			INestedWordAutomaton<LETTER, STATE> minuend,
			INestedWordAutomaton<LETTER, STATE> subtrahend,
			AutomatonEpimorphism<STATE> automatonEpimorhpism, 
			boolean minimize)
			throws OperationCanceledException 
	{
		m_Minuend = minuend;
		m_Subtrahend = subtrahend;
		m_Epimorphism = automatonEpimorhpism;
		m_StateFactory = minuend.getStateFactory();
		m_ContainedStatesHashMap = new HashMap<String, STATE>();
		if(minimize) s_Logger.error("Minimization not implemented.");

		s_Logger.info(startMessage());

		// initialize the result with the empty automaton
		m_Result = new NestedWordAutomaton<LETTER, STATE>(
				minuend.getInternalAlphabet(), minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(), minuend.getStateFactory());
		m_SinkState = m_StateFactory.createSinkStateContent();
		s_Logger.debug("Created Sink-State: " + m_SinkState.toString());
		
		// initializes the process by adding the initial states. Since there can
		// be many initial states, it adds all possible initial state pair combinations
		for (STATE init_m : m_Minuend.getInitialStates()) 
		{
			STATE init_s = m_Epimorphism.getMapping(init_m);
			if(init_s == null || !m_Subtrahend.getInitialStates().contains(init_s))
			{
				init_s = m_SinkState;
			}
			else
			{
				assert(m_Subtrahend.getStates().contains(init_s));
			}
			s_Logger.debug("Add initial state:" + init_m + "---" + init_s);			
			addState(init_m, init_s);
		}
		s_Logger.info(exitMessage());
	}

	String bl(boolean b)
	{
		return b ? "T" : "F";
	}
	
	/**
	 * (for computing the super difference) Adds a state into the result
	 * automaton. Respectively adds all necessary edges and states
	 * 
	 * @param r
	 *            first part of the label of the state
	 * @param s
	 *            second part of the label of the state
	 * @return
	 * 			  the state in the new automaton            
	 */
	private STATE addState(STATE r, STATE s) 
	{
		assert(m_Minuend.getStates().contains(r));		
		assert(s == m_SinkState ||  m_Subtrahend.getStates().contains(s));
		
		// if it does already exist, return that state
		String qLabel = r.toString() + "|" + s.toString();
		STATE existingState = m_ContainedStatesHashMap.get(qLabel);
		if (existingState != null) 
		{
			s_Logger.debug("State for " + qLabel + " already exists: "
					+ existingState.toString());
			return existingState;
		}

		// if not: create a new state "q" and add it into the superDifference automaton
		s_Logger.debug("Add state: " + qLabel + " created from: " + r.toString() + " and " + s.toString());
		STATE intersection = m_StateFactory.intersection(r, s);
		if(intersection == null) s_Logger.error("State factory returned no state!");
		s_Logger.debug("intersection: " + intersection.toString());
		m_ContainedStatesHashMap.put(qLabel, intersection);
	
		boolean isInitial = m_Minuend.isInitial(r) && (s == m_SinkState || m_Subtrahend.isInitial(s));
		boolean isFinal = m_Minuend.isFinal(r) && (s == m_SinkState || !m_Subtrahend.isFinal(s));
		
		s_Logger.debug("isFinal: " + isFinal);
		s_Logger.debug("isIniti: " + isInitial);
		
		m_Result.addState(isInitial, isFinal, intersection);

		// get the epimorph state
		STATE h_r = m_Epimorphism.getMapping(r);
		
		// check if there exists a mapping to r in the epimorphism
		if (h_r == s) 
		{
			s_Logger.debug("epimorph state: " + h_r.toString());
			// Traverse all edges = (r, label, r2) \in \delta

			for(OutgoingInternalTransition<LETTER, STATE> e : m_Minuend.internalSuccessors(r))
			{
				traverseEdge(e, r, s, intersection, e.getSucc(), 0, null);
			}
			
			for(OutgoingCallTransition<LETTER, STATE> e : m_Minuend.callSuccessors(r))
			{
				traverseEdge(e, r, s, intersection, e.getSucc(), 1, null);
			}

			for(OutgoingReturnTransition<LETTER, STATE> e : m_Minuend.returnSuccessors(r))
			{
				// get the hier pred (if not exists this could be created)
				STATE mapping = m_Epimorphism.getMapping(e.getHierPred());
				if(mapping != null) 
				{
					s_Logger.debug("found hier pred state mapping:" + mapping.toString());
					STATE hierPred = addState(e.getHierPred(), mapping);
					traverseEdge(e, r, s, intersection, e.getSucc(), 2, hierPred);
				}
				else
				{
					s_Logger.debug("found sink no hier pred mapping, took sink state");
				}
				STATE hierPred = addState(e.getHierPred(), m_SinkState);
				
				s_Logger.debug("hier pred is: " + hierPred);
				traverseEdge(e, r, s, intersection, e.getSucc(), 2, hierPred);
			}
			
		} 
		else
		{
			// we are in the sink state in the subtrahend automaton
			
			s_Logger.debug("No epimorph state found: hr:" + h_r + " r:" + r + " s: " + s);
			
			// Traverse all edges = (r, label, r2) \in \delta
			for(OutgoingInternalTransition<LETTER, STATE> e : m_Minuend.internalSuccessors(r))
			{
				// we know that we must take the sink state, since there is no epimorph state
				s_Logger.debug("follow label " + e.getLetter() + " and ...");
				s_Logger.debug("add target (sinked) state q2: " + e.getSucc());
				STATE q2 = addState(e.getSucc(), m_SinkState);
				s_Logger.debug("Traverse in sink state " + intersection + " with " + e.getLetter() + " to " + q2.toString());
				m_Result.addInternalTransition(intersection, e.getLetter(), q2);
			}

			for(OutgoingCallTransition<LETTER, STATE> e : m_Minuend.callSuccessors(r))
			{
				s_Logger.debug("follow label " + e.getLetter() + " and ...");
				s_Logger.debug("add target (sinked) state q2: " + e.getSucc());
				STATE q2 = addState(e.getSucc(), m_SinkState);
				s_Logger.debug("Traverse in sink state " + intersection + " with " + e.getLetter() + " to " + q2.toString());
				m_Result.addCallTransition(intersection, e.getLetter(), q2);
			}
			
			for(OutgoingReturnTransition<LETTER, STATE> e : m_Minuend.returnSuccessors(r))
			{
				s_Logger.debug("follow label " + e.getLetter() + " and ...");
				s_Logger.debug("add target (sinked) state q2: " + e.getSucc());
				
				STATE mapping = m_Epimorphism.getMapping(e.getHierPred());
				if(mapping != null) 
				{
					// Add the transition's hierarchical predecessor
					STATE hierPred = addState(e.getHierPred(), mapping);				
					// Add the transition's successor
					STATE q2 = addState(e.getSucc(), m_SinkState);	
					// Add the transition 				
					m_Result.addReturnTransition(intersection, hierPred, e.getLetter(), q2);
				}
				
				// Add the transition's hierarchical predecessor
				STATE hierPred = addState(e.getHierPred(), m_SinkState);								
				// Add the transition's successor
				STATE q2 = addState(e.getSucc(), m_SinkState);				
				// Add the transition 
				m_Result.addReturnTransition(intersection, hierPred, e.getLetter(), q2);
				
				s_Logger.debug("Traverse in sink state " + intersection + " with " + e.getLetter() + " to " + q2.toString());
			}			
		}

		return intersection;
	}

	/**
	 * Traverse an edge and add it to the new automatons.
	 * @param e the outgoing transition
	 * @param r the state of the subtrahend
	 * @param s the state of the minuend
	 * @param q the merged stated
	 * @param target the successor of the outgoing transition
	 * @param edgeType 0:internal, 1:call, 2:return
	 * @param hierPred hierarchical predecessor
	 */
	private void traverseEdge(
			Transitionlet<LETTER,STATE> e,
			STATE r, 
			STATE s, 
			STATE q,
			STATE target,
			int edgeType,
			STATE hierPred) 
	{
		LETTER label = e.getLetter();

		s_Logger.debug("Traverse edge: from " + r.toString() + " with " + label + " to " + target.toString());

		// find/construct the target state of the edge
		STATE q2 = null;
		// get the target state in the subtrahend automaton
		STATE h_r2 = m_Epimorphism.getMapping(target);
		s_Logger.debug("mapping of the target is: " + h_r2);
		
		// now we want to check if the subtrahend automaton has an epimorph state as well
		boolean targetExistsInMinuend = false;
		if(h_r2 != null)
		{
			switch(edgeType)
			{
			case 0:
				for(OutgoingInternalTransition<LETTER,STATE> e2 : m_Subtrahend.internalSuccessors(s, label))
				{
					if(e2.getSucc() == h_r2)
					{
						targetExistsInMinuend = true;
						break;
					}
				}
				break;
			case 1:
				for(OutgoingCallTransition<LETTER,STATE> e2 : m_Subtrahend.callSuccessors(s, label))
				{
					if(e2.getSucc() == h_r2)
					{
						targetExistsInMinuend = true;
						break;
					}
				}
				break;
			case 2:
				s_Logger.debug("hierPred for " + hierPred);
				for(OutgoingReturnTransition<LETTER,STATE> e2 : m_Subtrahend.returnSucccessors(s, hierPred, label))
				{
					if(e2.getSucc() == h_r2)
					{
						targetExistsInMinuend = true;
						break;
					}
				}
				break;
			}
		}
		
		
		
		// make sure that the target state q2 exists
		if (targetExistsInMinuend) 
		{
			s_Logger.debug("target state exists");
			// if that state and the corresponding edge with the same label exists
			q2 = addState(target, h_r2);
		} 
		else 
		{
			s_Logger.debug("target state exists not");
			// otherwise we fall in to the sink state
			q2 = addState(target, m_SinkState);
		}

//				s_Logger.debug("Adding the edge from " + q.toString() + " with " + label + " to " + q2.toString());
		
		switch(edgeType)
		{
		case 0:
			m_Result.addInternalTransition(q, label, q2);
			break;
		case 1:
			m_Result.addCallTransition(q, label, q2);
			break;
		case 2:
			m_Result.addReturnTransition(q, hierPred, label, q2);
			break;
		}
		
	}

	@Override
	public boolean checkResult(StateFactory stateFactory)
			throws OperationCanceledException 
	{
		// TODO Auto-generated method stub
		return false;
	}
}
