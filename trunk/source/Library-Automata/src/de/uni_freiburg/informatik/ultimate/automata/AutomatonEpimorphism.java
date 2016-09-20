/*
 * Copyright (C) 2012-2015 Jan Hättig (haettigj@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
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
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * Given two nondeterministic NWAs {@code minuend} and {@code subtrahend} a.
 * <p>
 * TODO Christian 2016-08-20: unfinished documentation
 * 
 * @author Jan Hättig (haettigj@informatik.uni-freiburg.de)
 * @param <STATE>
 *            Content. Type of the labels that are assigned to the states of the
 *            automata. In many cases you want to use {@link String} as {@link STATE} and your
 *            states are labeled, e.g., with "q0", "q1", ...
 */
public class AutomatonEpimorphism<STATE> {
	private static final String INVALID_STATE_NAME_MESSAGE = "Invalid state name: ";
	
	private final ILogger mLogger;
	
	private final Map<STATE, STATE> mEpimorphism;
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 */
	public AutomatonEpimorphism(final AutomataLibraryServices services) {
		mLogger = services.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mEpimorphism = new HashMap<>();
	}
	
	/**
	 * Creates the epimorphism for two automata from {@code nwa1} to {@code nwa2}. The Labels of
	 * {@code nwa1} have to be of type {@link String} and have to be of the following scheme:
	 * <blockquote>
	 * {@code l1_l2},
	 * </blockquote>
	 * where {@code l1} is the actual label of the state and {@code l2} is
	 * the label of the state of {@code nwa2} which it is epimorphic to.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param nwa1
	 *            automaton where the epimorphism is encoded in the labels
	 * @param nwa2
	 *            automaton where the epimorphism maps to
	 * @return an epimorphism structure from nwa1 to nwa2
	 */
	public static AutomatonEpimorphism<String> createFromAutomatonLabels(final AutomataLibraryServices services,
			final INestedWordAutomaton<String, String> nwa1, final INestedWordAutomaton<String, String> nwa2) {
		final AutomatonEpimorphism<String> epimorphism = new AutomatonEpimorphism<>(services);
		
		// traversing the states
		for (final String state1 : nwa1.getStates()) {
			final int indexOfUnderscore = state1.indexOf('_');
			if (indexOfUnderscore == -1) {
				continue;
			}
			
			// check that '_' is not the last char in the string
			if (indexOfUnderscore + 1 == state1.length()) {
				throw new IllegalArgumentException(INVALID_STATE_NAME_MESSAGE + state1);
			}
			
			// get the name of the epimorph state
			final String state2 = state1.substring(indexOfUnderscore + 1);
			
			// check that '_' does not occur multiple times
			if (state2.indexOf('_') != -1) {
				throw new IllegalArgumentException(INVALID_STATE_NAME_MESSAGE + state1);
			}
			
			// search the state in nwa2; if it is not found, error
			if (!nwa2.getStates().contains(state2)) {
				throw new IllegalArgumentException("Missing epimorphism partner for: " + state1);
			}
			
			// set the mapping from state1 to state2
			epimorphism.mEpimorphism.put(state1, state2);
		}
		
		return epimorphism;
	}
	
	/**
	 * Returns the state where the epimorphism points to.
	 * 
	 * @param source
	 *            source state
	 * @return target state under the epimorphism
	 */
	public STATE getMapping(final STATE source) {
		return mEpimorphism.get(source);
	}
	
	/**
	 * Inserts a new mapping of two states.
	 * 
	 * @param source
	 *            mapping from this state
	 * @param target
	 *            mapping to this state
	 */
	public void insert(final STATE source, final STATE target) {
		mEpimorphism.put(source, target);
	}
	
	/**
	 * Prints the object to the logger in <tt>DEBUG</tt> level.
	 */
	public void print() {
		if (mLogger.isDebugEnabled()) {
			for (final Entry<STATE, STATE> e : mEpimorphism.entrySet()) {
				mLogger.debug(e.getKey() + " --> " + e.getValue());
			}
		}
	}
}
