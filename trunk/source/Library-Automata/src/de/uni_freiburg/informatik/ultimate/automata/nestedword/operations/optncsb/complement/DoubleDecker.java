/*
 * Copyright (C) 2017 Yong Li (liyong@ios.ac.cn)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.complement;

import java.util.Objects;

public class DoubleDecker {

	private final int mDownState;
	private final int mUpState;

	public DoubleDecker(final int down, final int up) {
		mDownState = down;
		mUpState = up;
	}

	public int getDownState() {
		return mDownState;
	}

	public int getUpState() {
		return mUpState;
	}

	@Override
	public boolean equals(final Object other) {
		if (this == other) {
			return true;
		}
		if (other == null || getClass() != other.getClass()) {
			return false;
		}
		final DoubleDecker otherDecker = (DoubleDecker) other;
		return mDownState == otherDecker.mDownState && mUpState == otherDecker.mUpState;
	}

	@Override
	public int hashCode() {
		return Objects.hash(mDownState, mUpState);
	}

	@Override
	public String toString() {
		return "<down:" + mDownState + ", up:" + mUpState + ">";
	}

	public static final int EMPTY_DOWN_STATE = -1;

}
