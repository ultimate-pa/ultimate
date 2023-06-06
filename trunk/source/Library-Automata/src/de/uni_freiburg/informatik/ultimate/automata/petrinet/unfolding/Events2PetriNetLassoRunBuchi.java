/*
 * Copyright (C) 2022-2023 Daniel Küchler (kuechlerdaniel33@gmail.com)
 * Copyright (C) 2022-2023 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetLassoRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetNot1SafeException;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.PetriNetRun;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Given stem and loop events of supposed accepting lasso word, if valid, {@link PetriNetLassoRun} is built.
 *
 * @param <LETTER>
 * @param <PLACE>
 *
 * @author Daniel Küchler (kuechlerdaniel33@gmail.com)
 */
public class Events2PetriNetLassoRunBuchi<LETTER, PLACE> {
	private final BranchingProcess<LETTER, PLACE> mUnfolding;
	private final List<Event<LETTER, PLACE>> mConfigStemPart;
	private final List<Event<LETTER, PLACE>> mConfigLoopPart;

	public Events2PetriNetLassoRunBuchi(final List<Event<LETTER, PLACE>> configLoopPart,
			final List<Event<LETTER, PLACE>> configStemPart, final BranchingProcess<LETTER, PLACE> unfolding) {
		mUnfolding = unfolding;
		mConfigStemPart = configStemPart;
		mConfigLoopPart = configLoopPart;
	}

	public boolean isAccepted() {
		return mConfigLoopPart.stream().flatMap(x -> x.getTransition().getSuccessors().stream())
				.anyMatch(mUnfolding.getNet()::isAccepting);
	}

	/**
	 * Given loop and stem events, checks if the respective Transitions actually build a valid lasso-run in the
	 * Petri-Net.
	 */
	public PetriNetLassoRun<LETTER, PLACE> constructLassoRun() throws PetriNetNot1SafeException {
		final List<Transition<LETTER, PLACE>> stemTransitions =
				mConfigStemPart.stream().map(Event::getTransition).collect(Collectors.toList());
		final List<Transition<LETTER, PLACE>> loopTransitions =
				mConfigLoopPart.stream().map(Event::getTransition).collect(Collectors.toList());

		final Marking<PLACE> startMarking = new Marking<>(ImmutableSet.of(mUnfolding.getNet().getInitialPlaces()));

		final PetriNetRun<LETTER, PLACE> stemRun = constructRun(startMarking, stemTransitions);
		final PetriNetRun<LETTER, PLACE> loopRun =
				constructRun(stemRun.getMarking(stemRun.getLength() - 1), loopTransitions);

		return new PetriNetLassoRun<>(stemRun, loopRun);
	}

	/**
	 * Given a sorted List of transitions which build a valid firesequence, builds a valid {@PetriNetRun}.
	 *
	 * @param initialMarking
	 *            of the Petri-Net
	 * @param transitions,
	 *            the "sorted" Transitions which build the lasso-word
	 * @return A valid PetriNetRun
	 * @throws PetriNetNot1SafeException
	 */
	@SuppressWarnings("unchecked")
	private final PetriNetRun<LETTER, PLACE> constructRun(final Marking<PLACE> initialMarking,
			final List<Transition<LETTER, PLACE>> transitions) throws PetriNetNot1SafeException {
		final List<LETTER> word = new ArrayList<>();
		final List<Marking<PLACE>> markings = new ArrayList<>();
		markings.add(initialMarking);
		Marking<PLACE> currentMarking = initialMarking;
		for (final Transition<LETTER, PLACE> transition : transitions) {
			word.add(transition.getSymbol());
			currentMarking = currentMarking.fireTransition(transition);
			markings.add(currentMarking);
		}
		return new PetriNetRun<>(markings, new Word<>((LETTER[]) word.toArray()), transitions);
	}
}
