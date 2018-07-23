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

/**
 * A {@link OrdinaryDebugIdentifier} is a {@link DebugIdentifier} that represents an ordinary location (i.e., L1, L2,
 * etc.).
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class OrdinaryDebugIdentifier extends DebugIdentifier {

	private final int mLinenumber;
	private final int mOccurence;

	/**
	 * Constructor.
	 *
	 * @param linenumber
	 *            The linenumber.
	 * @param occurrence
	 *            A number larger or equal to 0 representing how often this linenumber has been seen.
	 */
	public OrdinaryDebugIdentifier(final int linenumber, final int occurrence) {
		if (occurrence < 0) {
			throw new IllegalArgumentException("negative occurence is not allowed");
		}
		mLinenumber = linenumber;
		mOccurence = occurrence;
	}

	public int getLinenumber() {
		return mLinenumber;
	}

	public int getOccurence() {
		return mOccurence;
	}

	@Override
	public String toString() {
		if (mOccurence == 0) {
			return "L" + mLinenumber;
		}
		return new StringBuilder().append("L").append(mLinenumber).append("-").append(mOccurence).toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + mLinenumber;
		result = prime * result + mOccurence;
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
		final OrdinaryDebugIdentifier other = (OrdinaryDebugIdentifier) obj;
		if (mLinenumber != other.mLinenumber) {
			return false;
		}
		if (mOccurence != other.mOccurence) {
			return false;
		}
		return true;
	}

}
