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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.HashMap;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;

/**
 * Given two nondeterministic NWAs nwa_minuend and nwa_subtrahend a
 * 
 * 
 * @author haettigj@informatik.uni-freiburg.de
 * 
 * @param <LETTER>
 *            Symbol. Type of the elements of the alphabet over which the
 *            automata are defined.
 * @param <STATE>
 *            Content. Type of the labels that are assigned to the states of
 *            automata. In many cases you want to use String as STATE and your
 *            states are labeled e.g. with "q0", "q1", ...
 */
public class AutomatonEpimorphism<STATE> {

	// For status output
	private static Logger s_Logger = NestedWordAutomata.getLogger();

	private HashMap<STATE, STATE> m_epimorphism;

	public AutomatonEpimorphism() {
		m_epimorphism = new HashMap<STATE, STATE>();
	}

	/**
	 * Creates the epimorphism for two automatons from a1 to a2. The Labels of
	 * a1 have to be of type string and have to be of the following scheme:
	 * "<l1>_<l2>", where "<l1>" is the actual label of the state and <l2> is
	 * the label of the node of a2, which it is epimorph to
	 * 
	 * @param a1
	 *            automaton where the epimorphism to to is encoded in the labels
	 * @param a2
	 *            automaton where the epimorphism maps to
	 * @return an epimorphism structure from a1 to a2
	 */
	public static AutomatonEpimorphism<String> createFromAutomatonLabels(
			INestedWordAutomatonOldApi<String, String> a1,
			INestedWordAutomatonOldApi<String, String> a2) {
		AutomatonEpimorphism<String> epimorphism = new AutomatonEpimorphism<String>();

		// traversing the states
		for (String state1 : a1.getStates()) {
			if (state1.contains("_")) {

				// check that "_" is not the last char in the string
				if (state1.indexOf("_") + 1 == state1.length()) {
					s_Logger.error("Invalid state name: " + state1);
				}

				// get the name of the epimorph state
				String epimorphState = state1
						.substring(state1.indexOf("_") + 1);

				// check that "_" does not occur multiple times
				if (epimorphState.indexOf("_") != -1) {
					s_Logger.error("Invalid state name: " + state1);
				}

				// search the state in a2
				String state2 = null;
				for (String s : a2.getStates()) {
					if (s.equals(epimorphState)) {
						state2 = s;
					}
				}

				// if it is not found, error
				if (state2 == null) {
					s_Logger.error("Missing epimorphism partner for: " + state1);
				}

				// set the mapping from state1 to state2
				epimorphism.m_epimorphism.put(state1, state2);
			}
		}

		return epimorphism;
	}
	
	/**
	 * Returns the state, where the epimorphism points to
	 * @param s
	 */
	public STATE getMapping(STATE s)
	{
		return m_epimorphism.get(s);
	}
	
	public void insert(STATE from, STATE to)
	{
		m_epimorphism.put(from, to);
	}

	public void Print() 
	{
		for(Entry<STATE, STATE> e : m_epimorphism.entrySet())
		{
			s_Logger.debug(e.getKey().toString() + " --> " + e.getValue());
		}		
	}
}
