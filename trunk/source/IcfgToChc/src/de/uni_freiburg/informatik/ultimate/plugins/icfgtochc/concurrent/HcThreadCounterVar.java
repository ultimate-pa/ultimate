/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * A variable that counts the number of started resp. of terminated threads. These variables are used for a
 * thread-modular encoding of postconditions.
 *
 * The thread-modular encoding of postconditions works as follows:
 * <ol>
 * <li>The number of started threads is incremented each time one of the initially running threads takes its first
 * step.</li>
 * <li>The number of terminated threads is incremented each time one of the initially running threads terminates.</li>
 * <li>If an initially running thread has terminated, and the numbers of started and terminated threads are equal, then
 * the postcondition must hold.</li>
 * </ol>
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class HcThreadCounterVar implements IHcReplacementVar {

	// An instance either represents the number of started threads (if this boolean is true) or of terminated threads
	private final boolean mIsStarted;
	private final Sort mSort;

	public HcThreadCounterVar(final boolean isStarted, final Sort sort) {
		mIsStarted = isStarted;
		mSort = sort;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	public boolean isStarted() {
		return mIsStarted;
	}

	public boolean isTerminated() {
		return !mIsStarted;
	}

	@Override
	public String toString() {
		return mIsStarted ? "~started" : "~terminated";
	}

	@Override
	public int hashCode() {
		return Objects.hash(mIsStarted);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final HcThreadCounterVar other = (HcThreadCounterVar) obj;
		return mIsStarted == other.mIsStarted;
	}
}
