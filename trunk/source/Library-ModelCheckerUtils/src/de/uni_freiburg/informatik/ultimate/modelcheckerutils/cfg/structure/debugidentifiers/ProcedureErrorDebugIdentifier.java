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

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * A {@link ProcedureErrorDebugIdentifier} is a debug identifier for an {@link IcfgLocation} that represents an error
 * location of a procedure.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class ProcedureErrorDebugIdentifier extends StringDebugIdentifier {

	public enum ProcedureErrorType {
		ASSERT_VIOLATION, REQUIRES_VIOLATION, ENSURES_VIOLATION, INUSE_VIOLATION
	}

	private final int mId;
	private final ProcedureErrorType mType;

	public ProcedureErrorDebugIdentifier(final String procedureName, final int uniqueNumber,
			final ProcedureErrorType type) {
		super(procedureName);
		mId = uniqueNumber;
		mType = Objects.requireNonNull(type);
	}

	@Override
	public String toString() {
		return new StringBuilder().append(getPrefix()).append("Err").append(mId).append(mType).toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + mId;
		result = prime * result + mType.hashCode();
		result = prime * result + getPrefix().hashCode();
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final ProcedureErrorDebugIdentifier other = (ProcedureErrorDebugIdentifier) obj;
		if (mId != other.mId) {
			return false;
		}
		if (mType != other.mType) {
			return false;
		}
		if (!getPrefix().equals(other.getPrefix())) {
			return false;
		}
		return true;
	}
}
