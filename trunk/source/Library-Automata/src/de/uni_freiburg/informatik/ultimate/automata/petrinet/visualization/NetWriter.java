/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.visualization;

import java.io.PrintWriter;
import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.GeneralAutomatonPrinter;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.ITransition;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.BoundedPetriNet;

/**
 * Prints a {@link BoundedPetriNet}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class NetWriter<LETTER, STATE> extends GeneralAutomatonPrinter {
	private final Map<LETTER, String> mAlphabet;
	private final Map<STATE, String> mPlacesMapping;

	/**
	 * @param writer
	 *            Print writer.
	 * @param name
	 *            Petri net name
	 * @param net
	 *            Petri net
	 */
	@SuppressWarnings({ "squid:S1699", "fb-contrib:PCOA_PARTIALLY_CONSTRUCTED_OBJECT_ACCESS" })
	public NetWriter(final PrintWriter writer, final String name, final BoundedPetriNet<LETTER, STATE> net) {
		super(writer);
		mAlphabet = getAlphabetMapping(net.getAlphabet());
		mPlacesMapping = getPlacesMapping(net.getPlaces());

		print("PetriNet ");
		print(name);
		printAutomatonPrefix();
		printAlphabet();
		printPlaces();
		printTransitions(net);
		printInitialMarking(net.getInitialPlaces());
		printAcceptingPlaces(net.getAcceptingPlaces());
		printAutomatonSuffix();
		finish();
	}

	protected abstract Map<LETTER, String> getAlphabetMapping(final Collection<LETTER> alphabet);

	protected abstract Map<STATE, String>
			getPlacesMapping(final Collection<STATE> places);

	protected final void printElementPrefix(final String string) {
		print(String.format("\t%s = ", string));
	}

	private void printAlphabet() {
		printCollectionPrefix("alphabet");
		printValues(mAlphabet);
		printCollectionSuffix();
	}

	private void printPlaces() {
		printCollectionPrefix("places");
		printValues(mPlacesMapping);
		printCollectionSuffix();
	}

	private void printTransitions(final BoundedPetriNet<LETTER, STATE> net) {
		printlnCollectionPrefix("transitions");
		for (final ITransition<LETTER, STATE> transition : net.getTransitions()) {
			printTransition(transition, net);
		}
		printTransitionsSuffix();
		print(',');
		print(NEW_LINE);
	}

	private void printTransition(final ITransition<LETTER, STATE> transition, BoundedPetriNet<LETTER, STATE> net) {
		printOneTransitionPrefix();
		printMarking(net.getPredecessors(transition));
		print(' ');
		print(mAlphabet.get(transition.getSymbol()));
		print(' ');
		printMarking(net.getSuccessors(transition));
		printOneTransitionSuffix();
	}

	private void printMarking(final Iterable<STATE> marking) {
		print('{');
		for (final STATE place : marking) {
			printElement(mPlacesMapping.get(place));
		}
		print('}');
	}

	private void printInitialMarking(final Iterable<STATE> initialMarking) {
		printElementPrefix("initialMarking");
		printMarking(initialMarking);
		println(',');
	}

	private void printAcceptingPlaces(final Iterable<STATE> acceptingPlaces) {
		printElementPrefix("acceptingPlaces");
		printMarking(acceptingPlaces);
		print(NEW_LINE);
	}
}
