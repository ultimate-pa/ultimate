/*
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.petrinet.unfolding.BranchingProcess;

/**
 * @author Miriam Lagunes (miriam.lagunes@students.uni-freiburg.de)
 *
 * @param <PLACE>
 *            The type of places in the Petri program
 * @param <LETTER>
 *            The type of statements in the Petri program
 */

public final class Crown<PLACE, LETTER> {

	private final Set<Rook<PLACE, LETTER>> mCrown;

	private final BranchingProcess<LETTER, PLACE> mBp;

	public Crown(final BranchingProcess<LETTER, PLACE> bp) {
		mBp = bp;
		mCrown = new HashSet<>();
	}

	public Set<Rook<PLACE, LETTER>> getRooks() {
		return mCrown;
	}

	public void addRook(final Rook<PLACE, LETTER> rook) {
		mCrown.add(rook);
	}

	public void addRook(final Set<Rook<PLACE, LETTER>> rooks) {
		mCrown.addAll(rooks);
	}

	public boolean removeRook(final Rook<PLACE, LETTER> rook) {
		if (mCrown.contains(rook)) {
			mCrown.remove(rook);
			return true;
		}
		return false;
	}

	public boolean removeRook(final Set<Rook<PLACE, LETTER>> rooks) {
		if (mCrown.containsAll(rooks)) {
			mCrown.removeAll(rooks);
			return true;
		}
		return false;
	}

}
