/*
 * Copyright (C) 2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.alternating.visualization;

import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.alternating.AlternatingAutomaton;

/**
 * Constructor takes a AlternatingAutomaton and writes it to a testfile.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class AlternatingAutomatonWriter<LETTER, STATE> extends GeneralAutomatonPrinter {
	private final AlternatingAutomaton<LETTER, STATE> mAa;

	/**
	 * @param writer
	 *            Print writer.
	 * @param name
	 *            automaton name
	 * @param automaton
	 *            alternating automaton
	 */
	public AlternatingAutomatonWriter(final PrintWriter writer, final String name,
			final AlternatingAutomaton<LETTER, STATE> automaton) {
		super(writer);
		mAa = automaton;

		print("AlternatingAutomaton ");
		print(name);
		printAutomatonPrefix();
		println(mAa.toString());
		// printAlphabet(mAa.getAlphabet());
		// printExistentialStates(mAa.getExistentialStates());
		// printUniversalStates(mAa.getUniversalStates());
		// printInitialStates(mAa.getInitialStates());
		// printFinalStates(mAa.getFinalStates());
		// printInternalTransitions(mAa.getTransitionsMap());
		printAutomatonSuffix();
		finish();
	}

	/*
	 * private void printAlphabet(Set<LETTER> set) { mprintWriter.print(TAB + "alphabet = { "); for (LETTER letter :
	 * set) { mprintWriter.print(letter + ' '); } mprintWriter.print("},\n"); }
	 *
	 * private void printExistentialStates(Set<STATE> set) { mprintWriter.print(TAB + "existentialStates = { "); for
	 * (STATE state : set) { mprintWriter.print(state + ' '); } mprintWriter.print("},\n"); }
	 *
	 * private void printUniversalStates(Set<STATE> set) { mprintWriter.print(TAB + "universalStates = { "); for (STATE
	 * state : set) { mprintWriter.print(state + ' '); } mprintWriter.print("},\n"); }
	 *
	 * private void printInitialStates(Set<STATE> set) { mprintWriter.print(TAB + "initialStates = { "); for (STATE
	 * state : set) { mprintWriter.print(state + ' '); } mprintWriter.print("},\n"); }
	 *
	 * private void printFinalStates(Set<STATE> set) { mprintWriter.print(TAB + "finalStates = { "); for (STATE state :
	 * set) { mprintWriter.print(state + ' '); } mprintWriter.print("},\n"); }
	 *
	 * private void printInternalTransitions(Map<STATE, Map<LETTER, Set<STATE>>> map) { mprintWriter.println(TAB +
	 * "internalTransitions = {"); for (Entry<STATE, Map<LETTER, Set<STATE>>> entry : map.entrySet()) { STATE pre =
	 * entry.getKey(); Map<LETTER, Set<STATE>> transitionsMap = entry.getValue(); if (transitionsMap != null) {// state
	 * has no outgoing transitions, so nothing has to be printed for (Entry<LETTER, Set<STATE>> entry1 :
	 * transitionsMap.entrySet()) { LETTER letter = entry1.getKey(); Set<STATE> succStates = entry1.getValue(); for
	 * (STATE succ : succStates) { printInternalTransition(pre, letter, succ); } } }
	 *
	 * } mprintWriter.println("\t},"); }
	 *
	 * private void printInternalTransition(STATE pre, LETTER letter, STATE succ) { mprintWriter.println("\t\t (" + pre
	 * + ' ' + letter + ' ' + succ + ')' ); }
	 */
}
