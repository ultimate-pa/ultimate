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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Set;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.EnumerateWords;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * A class that checks if the inputs for dynamic partial order reduction satisfy certain preconditions.
 *
 * Mostly useful for debugging.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class DPORInputChecker {
	private DPORInputChecker() {
		// static class
	}

	public static <L, S> void checkLocalMembranes(final INestedWordAutomaton<L, S> aut,
			final IMembranes<L, S> membranes) {
		for (final var s : aut.getStates()) {
			checkLocalMembrane(aut, s, membranes.getMembraneSet(s));
		}
	}

	public static <L, S> void checkLocalMembrane(final INestedWordAutomaton<L, S> aut, final S state,
			final Set<L> membrane) {
		// check the membrane is local
		for (final var x : membrane) {
			final var local =
					StreamSupport.stream(aut.internalSuccessors(state, x).spliterator(), false).findAny().isPresent();
			assert local : "non-local letter " + x + " in membrane at state " + state;
		}

		// check it is a membrane
		final var ctex = EnumerateWords.stream(aut, state)
				.filter(w -> DataStructureUtils.haveEmptyIntersection(w.asSet(), membrane)).findAny();
		assert ctex.isEmpty() : "Accepted word " + ctex.get() + " does not go through membrane " + membrane
				+ " at state " + state;
	}
}
