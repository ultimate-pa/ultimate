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
package de.uni_freiburg.informatik.ultimate.automata.tree.visualization;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/**
 * Constructor takes a TreeAutomaton and writes it to a testfile.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class TreeAutomatonWriter<LETTER extends IRankedLetter, STATE> extends GeneralAutomatonPrinter {

	private final TreeAutomatonBU<LETTER, STATE> mTreeAutomaton;
	/**
	 * character used to quote states
	 */
	private final String mQuote;

	public TreeAutomatonWriter(final PrintWriter writer, final String name,
			final TreeAutomatonBU<LETTER, STATE> automaton) {
		// default is to use a quote symbol
		this(writer, name, automaton, "\"");
	}

	/**
	 * @param writer
	 *            Print writer.
	 * @param name
	 *            automaton name
	 * @param automaton
	 *            alternating automaton
	 */
	protected TreeAutomatonWriter(final PrintWriter writer, final String name,
			final TreeAutomatonBU<LETTER, STATE> automaton, final String quote) {
		super(writer);
		mTreeAutomaton = automaton;
		mQuote = quote;

		final Map<LETTER, String> alphabetMapping = getAlphabetMapping(mTreeAutomaton.getAlphabet());
		final Map<STATE, String> stateMapping = getStateMapping(mTreeAutomaton.getStates());

		print("TreeAutomaton ");
		print(name);
		print(" = ");
		print("TreeAutomaton (\n");
		printAlphabet(mTreeAutomaton.getAlphabet(), alphabetMapping);
		printStates(mTreeAutomaton.getStates(), stateMapping);
		printFinalStates(mTreeAutomaton.getFinalStates(), stateMapping);
		printTransitionTable(mTreeAutomaton.getRules(), alphabetMapping, stateMapping);
		printAutomatonSuffix();
		finish();
	}

	private void printTransitionTable(final Iterable<TreeAutomatonRule<LETTER, STATE>> rules,
			final Map<LETTER, String> alphabetMapping, final Map<STATE, String> stateMapping) {
		final StringBuilder transitionTable = new StringBuilder();

		transitionTable.append("\ttransitionTable = {");

		for (final TreeAutomatonRule<LETTER, STATE> rule : rules) {
			if (transitionTable.length() > 0) {
				transitionTable.append("\n");
			}
			final StringBuilder src = new StringBuilder();
			for (final STATE st : rule.getSource()) {
				if (src.length() > 0) {
					src.append(" ");
				}
				src.append(mQuote);
				src.append(stateMapping.get(st));
				src.append(mQuote);
			}
			final StringBuilder dest = new StringBuilder();
			dest.append(mQuote);
			dest.append(stateMapping.get(rule.getDest()));
			dest.append(mQuote);

			final StringBuilder letter = new StringBuilder();
			letter.append(mQuote);
			letter.append(alphabetMapping.get(rule.getLetter()));
			letter.append(mQuote);
			transitionTable.append(String.format("\t\t((%s) %s %s)", src, letter, dest));
		}

		transitionTable.append("}");

		println(transitionTable.toString());
	}

	private void printFinalStates(final Set<STATE> originalFinalStates, final Map<STATE, String> stateMapping) {

		final StringBuilder finalStates = new StringBuilder();

		finalStates.append("\tfinalStates = {");
		for (final STATE state : originalFinalStates) {
			if (finalStates.length() > 0) {
				finalStates.append(" ");
			}
			finalStates.append(mQuote);
			finalStates.append(stateMapping.get(state));
			finalStates.append(mQuote);
		}
		finalStates.append("},");
		println(finalStates.toString());
	}

	private void printStates(final Set<STATE> originalStates, final Map<STATE, String> stateMapping) {
		final StringBuilder states = new StringBuilder();
		states.append("\tstates = {");
		for (final STATE state : originalStates) {
			if (states.length() > 0) {
				states.append(" ");
			}
			states.append(mQuote);
			states.append(stateMapping.get(state));
			states.append(mQuote);
		}
		states.append("},");
		println(states.toString());
	}

	private void printAlphabet(final Set<LETTER> originalAlphabet, final Map<LETTER, String> alphabetMapping) {
		final StringBuilder alphabet = new StringBuilder();
		alphabet.append("\talphabet = {");
		for (final LETTER letter : originalAlphabet) {
			if (alphabet.length() > 0) {
				alphabet.append(" ");
			}
			alphabet.append(mQuote);
			alphabet.append(alphabetMapping.get(letter));
			alphabet.append(mQuote);
		}
		alphabet.append("},");
		println(alphabet.toString());
	}

	protected Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet) {
		final Map<LETTER, String> alphabetMapping = new HashMap<>();
		for (final LETTER letter : mTreeAutomaton.getAlphabet()) {
			alphabetMapping.put(letter, letter.toString());
		}
		return alphabetMapping;
	}

	protected Map<STATE, String> getStateMapping(final Collection<STATE> states) {
		final Map<STATE, String> stateMapping = new HashMap<>();
		for (final STATE state : mTreeAutomaton.getStates()) {
			stateMapping.put(state, state.toString());
		}
		return stateMapping;
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
