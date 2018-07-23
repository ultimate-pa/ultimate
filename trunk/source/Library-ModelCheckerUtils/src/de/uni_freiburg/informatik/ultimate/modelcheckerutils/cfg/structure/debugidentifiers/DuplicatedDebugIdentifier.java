/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers;

import java.util.Objects;

/**
 * A {@link DuplicatedDebugIdentifier} is a {@link DebugIdentifier} that consists of another debug identifier and a
 * number.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class DuplicatedDebugIdentifier extends DebugIdentifier {

	private final DebugIdentifier mDebugIdentifier;
	private final int mDuplication;

	public DuplicatedDebugIdentifier(final DebugIdentifier debugIdentifier, final int duplication) {
		if (duplication < 0) {
			throw new IllegalArgumentException();
		}
		mDebugIdentifier = Objects.requireNonNull(debugIdentifier);
		mDuplication = duplication;
	}

	@Override
	public String toString() {
		return mDebugIdentifier.toString() + "-D" + mDuplication;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDebugIdentifier == null) ? 0 : mDebugIdentifier.hashCode());
		result = prime * result + mDuplication;
		return result;
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
		final DuplicatedDebugIdentifier other = (DuplicatedDebugIdentifier) obj;
		if (mDebugIdentifier == null) {
			if (other.mDebugIdentifier != null) {
				return false;
			}
		} else if (!mDebugIdentifier.equals(other.mDebugIdentifier)) {
			return false;
		}
		if (mDuplication != other.mDuplication) {
			return false;
		}
		return true;
	}

}
