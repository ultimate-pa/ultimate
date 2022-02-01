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

import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * Represents a transition whose guard is a conjunction of atomic counter
 * guards. In order to represent transitions whose guards contain also
 * disjunctions we bring the guard in DNF and make a copy of the transition.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ConjunctiveTransition<LETTER, STATE> {
	final STATE mPredecessor;
	final STATE mSuccessor;
	final LETTER mLetter;
	final ConjunctiveCounterFormula mGuard;
	final List<AtomicCounterAssingment> mAssignment;

	public ConjunctiveTransition(final STATE predecessor, final STATE successor, final LETTER letter,
			final ConjunctiveCounterFormula guard, final List<AtomicCounterAssingment> assignment) {
		super();
		Objects.nonNull(predecessor);
		Objects.nonNull(successor);
		Objects.nonNull(letter);
		Objects.nonNull(guard);
		Objects.nonNull(assignment);
		mPredecessor = predecessor;
		mSuccessor = successor;
		mLetter = letter;
		mGuard = guard;
		mAssignment = assignment;
	}

	public STATE getPredecessor() {
		return mPredecessor;
	}

	public STATE getSuccessor() {
		return mSuccessor;
	}

	public LETTER getLetter() {
		return mLetter;
	}

	public ConjunctiveCounterFormula getGuard() {
		return mGuard;
	}

	public List<AtomicCounterAssingment> getAssignment() {
		return Collections.unmodifiableList(mAssignment);
	}

}