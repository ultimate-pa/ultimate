/*
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.counting.datastructures;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;

/**
 * Prints a {@link CountingAutomatonDataStructure} in our ATS format.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class CaDatastructureWriter<LETTER, STATE> extends GeneralAutomatonPrinter {
	private final Map<LETTER, String> mAlphabet;
	private final Map<STATE, String> mStateMapping;

	public CaDatastructureWriter(final PrintWriter writer, final String name,
			final CountingAutomatonDataStructure<LETTER, STATE> ca) {
		super(writer);
		mAlphabet = getToStringMapping(ca.getAlphabet());
		mStateMapping = getToStringMapping(ca.getStates());

		print("CountingAutomaton ");
		print(name);
		printAutomatonPrefix();
		printAlphabet();
		printCounters(ca.getCounters());
		printStates();
		printConditions("initialConditions", ca.getInitialConditions());
		printConditions("finalConditions", ca.getAcceptingConditions());
		printTransitions(ca);
		printAutomatonSuffix();
		finish();
	}

	private static <E> Map<E, String> getToStringMapping(final Collection<E> elements) {
		final LinkedHashMap<E, String> map = new LinkedHashMap<>();
		elements.stream().forEach(x -> map.put(x, quoteAndReplaceBackslashes(x)));
		return map;
	}

	protected final void printElementPrefix(final String string) {
		print(String.format("\t%s = ", string));
	}

	private void printAlphabet() {
		printCollectionPrefix("alphabet");
		printValues(mAlphabet);
		printCollectionSuffix();
	}

	private void printStates() {
		printCollectionPrefix("states");
		printValues(mStateMapping);
		printCollectionSuffix();
	}

	private void printCounters(final Set<String> counters) {
		printCollectionPrefix("counters");
		printCollection(counters);
		printCollectionSuffix();
	}

	private void printConditions(final String kindOfConditions, final Map<STATE, Set<ConjunctiveCounterFormula>> map) {
		printCollectionPrefix(kindOfConditions);
		print(NEW_LINE);
		for (final Entry<STATE, Set<ConjunctiveCounterFormula>> entry : map.entrySet()) {
			printOneTransitionPrefix();
			print(mStateMapping.get(entry.getKey()));
			print(' ');
			printDisjunction(entry.getValue());
			printOneTransitionSuffix();
		}
		printTransitionsSuffix();
		print(',');
		print(NEW_LINE);
	}

	private void printDisjunction(final Set<ConjunctiveCounterFormula> disunction) {
		final String formulaAsString;
		if (disunction.isEmpty()) {
			formulaAsString = "false";
		} else if (disunction.size() == 1) {
			formulaAsString = disunction.iterator().next().toString();
		} else {
			formulaAsString = String.format("(or %s)",
					disunction.stream().map(Object::toString).collect(Collectors.joining(" ")));
		}
		print(quoteAndReplaceBackslashes(formulaAsString));
	}

	private void printTransitions(final CountingAutomatonDataStructure<LETTER, STATE> ca) {
		printlnCollectionPrefix("transitions");
		for (final STATE state : ca.getStates()) {
			for (final ConjunctiveTransition<LETTER, STATE> conjTrans : ca.getOutgoingTransitions(state)) {
				printOneTransitionPrefix();
				print(mStateMapping.get(conjTrans.getPredecessor()));
				print(' ');
				print(mAlphabet.get(conjTrans.getLetter()));
				print(' ');
				print(QUOTE);
				print(conjTrans.getGuard().toString());
				print(QUOTE);
				print(' ');
				print('{');
				final String updateList = conjTrans.getAssignment().stream().map(Object::toString)
						.collect(Collectors.joining(","));
				print(updateList);
				print('}');
				print(' ');
				print(mStateMapping.get(conjTrans.getSuccessor()));
				printOneTransitionSuffix();
			}
		}
		printTransitionsSuffix();
		print(NEW_LINE);
	}
}
