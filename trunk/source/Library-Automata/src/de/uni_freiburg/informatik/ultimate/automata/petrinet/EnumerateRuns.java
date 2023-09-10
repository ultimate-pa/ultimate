/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.petrinet;

import java.util.ArrayList;
import java.util.List;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.netdatastructures.Transition;
import de.uni_freiburg.informatik.ultimate.util.BFSIterator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Enumerates all accepting runs of a given Petri net, in increasing length.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public class EnumerateRuns {
	public static <L, P> Iterable<PetriNetRun<L, P>> enumerate(final IPetriNet<L, P> net) {
		return () -> new RunEnumerator<>(net);
	}

	public static <L, P> Stream<PetriNetRun<L, P>> stream(final IPetriNet<L, P> net) {
		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(new RunEnumerator<>(net),
				Spliterator.ORDERED | Spliterator.IMMUTABLE), false);
	}

	private static class RunEnumerator<L, P> extends BFSIterator<Marking<P>, Transition<L, P>, PetriNetRun<L, P>> {
		private final IPetriNet<L, P> mNet;

		public RunEnumerator(final IPetriNet<L, P> net) {
			super(List.of(getInitialMarking(net)));
			mNet = net;
		}

		private static <P> Marking<P> getInitialMarking(final IPetriNet<?, P> net) {
			return new Marking<>(ImmutableSet.copyOf(net.getInitialPlaces()));
		}

		@Override
		protected Iterable<Transition<L, P>> getOutgoing(final Marking<P> marking) {
			return mNet.getTransitions().stream().filter(marking::isTransitionEnabled).collect(Collectors.toList());
		}

		@Override
		protected Marking<P> getSuccessor(final Marking<P> marking, final Transition<L, P> transition) {
			try {
				return marking.fireTransition(transition);
			} catch (final PetriNetNot1SafeException e) {
				throw new IllegalStateException(e);
			}
		}

		@Override
		protected boolean isTarget(final Marking<P> marking) {
			return mNet.isAccepting(marking);
		}

		@Override
		protected PetriNetRun<L, P> finish(final ImmutableList<Pair<Marking<P>, Transition<L, P>>> stack,
				final Marking<P> finalMarking) {
			final L[] letters = (L[]) new Object[stack.size()];
			final var markings = new ArrayList<Marking<P>>();
			final var transitions = new ArrayList<Transition<L, P>>();

			markings.add(finalMarking);
			int i = stack.size() - 1;
			for (final var frame : stack) {
				letters[i] = frame.getSecond().getSymbol();
				transitions.add(0, frame.getSecond());
				markings.add(0, frame.getFirst());
				i--;
			}

			return new PetriNetRun<L, P>(markings, new Word<>(letters), transitions);
		}
	}
}
