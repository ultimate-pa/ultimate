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
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
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
	private final INestedWordAutomaton<LETTER, STATE> m_minuend;
	private final INestedWordAutomaton<LETTER, STATE> m_subtrahend;
	private final AutomatonEpimorphism<STATE> m_epimorphism;
	private final NestedWordAutomaton<LETTER, STATE> m_Result;
	private final STATE m_sinkState;
	private final HashMap<String, STATE> m_containedStatesHashMap;
	private final StateFactory<STATE> m_stateFactory;

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
				+ m_minuend.sizeInformation() + ". Subtrahend "
				+ m_subtrahend.sizeInformation();
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
	 *            the automaton automatism
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
		m_minuend = minuend;
		m_subtrahend = subtrahend;
		m_epimorphism = automatonEpimorhpism;
		m_stateFactory = minuend.getStateFactory();
		m_containedStatesHashMap = new HashMap<String, STATE>();
		if(minimize) s_Logger.error("Minimization not implemented.");

		s_Logger.info(startMessage());

		// initialize the result with the empty automaton
		m_Result = new NestedWordAutomaton<LETTER, STATE>(
				minuend.getInternalAlphabet(), minuend.getCallAlphabet(),
				minuend.getReturnAlphabet(), minuend.getStateFactory());
		m_sinkState = m_stateFactory.createSinkStateContent();

		// initializes the process by adding the initial states. Since there can
		// be many initial states, it adds all possible initial state pairs
		for (STATE init_m : m_minuend.getInitialStates()) 
		{
			for (STATE init_s : m_subtrahend.getInitialStates())
			{
				AddState(init_m, init_s);
			}
		}
		s_Logger.info(exitMessage());
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
	private STATE AddState(STATE r, STATE s) 
	{
		// if it does already exist, return that state
		String qLabel = r.toString() + "|" + s.toString();
		STATE existingState = m_containedStatesHashMap.get(qLabel);
		if (existingState != null) 
		{
			s_Logger.debug("State for " + qLabel + " already exists: "
					+ existingState.toString());
			return existingState;
		}

		// if not: create a new state "q" and add it into the superDifference automaton
		s_Logger.debug("Add state: " + qLabel);
		STATE q = m_stateFactory.intersection(r, s);
		m_containedStatesHashMap.put(qLabel, q);
		m_Result.addState(
				m_minuend.isInitial(r) && m_subtrahend.isInitial(s),
				m_minuend.isFinal(r) && !m_subtrahend.isFinal(s),
				q);

		// get the epimorph state
		STATE h_r = m_epimorphism.getMapping(r);

		// check if there exists a mapping to r in the epimorphism
		if (h_r == s) 
		{
			s_Logger.debug("Epimorph state to r found");
			// Traverse all edges = (r, label, r2) \in \delta
			for(OutgoingInternalTransition<LETTER, STATE> e : m_minuend.internalSuccessors(r))
			{
				LETTER label = e.getLetter();
				STATE target = e.getSucc();

				s_Logger.debug("Found edge: from " + r.toString() + " with " + label + " to " + target.toString());

				// find/construct the target state of the edge
				STATE q2 = null;
				// get the target state in the subtrahend automaton
				STATE h_r2 = m_epimorphism.getMapping(target);
				
				boolean target_exists = false;
				for(OutgoingInternalTransition<LETTER,STATE> e2 : m_subtrahend.internalSuccessors(h_r, label))
				{
					if(e2.getSucc() == h_r2)
					{
						target_exists = true;
						break;
					}
				}
				if (target_exists) 
				{
					// if that state and the corresponding edge with the same label exists
					q2 = AddState(target, h_r2);
				} 
				else 
				{
					// otherwise we fall in to the sink state
					q2 = AddState(target, m_sinkState);
				}

				s_Logger.debug("Adding the edge from " + q.toString() + " with " + label + " to " + q2.toString());
				m_Result.addInternalTransition(q, label, q2);
			}
		} 
		else 
		{
			s_Logger.debug("No epimorph state found");
			
			// Traverse all edges = (r, label, r2) \in \delta		
			for(OutgoingInternalTransition<LETTER, STATE> e : m_minuend.internalSuccessors(r))
			{
				LETTER label = e.getLetter();
				STATE r2 = e.getSucc();
				s_Logger.debug("Found edge: from " + r.toString() + " with " + label + " to " + r2.toString());
				
				// we know that we must take the sink state, since there is no epimorph state
				STATE q2 = AddState(r2, m_sinkState);
				s_Logger.debug("Adding the edge from " + q.toString() + " with " + label + " to " + q2.toString());
				m_Result.addInternalTransition(q, label, q2);
			}
		}

		return q;
	}

	@Override
	public boolean checkResult(StateFactory stateFactory)
			throws OperationCanceledException 
	{
		// TODO Auto-generated method stub
		return false;
	}
}
