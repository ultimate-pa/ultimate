/*
 * Copyright (C) 2023 Manuel Bentele (bentele@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessParser plug-in.
 *
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

/**
 * @author Manuel Bentele (bentele@informatik.uni-freiburg.de)
 */
public class FormatVersion implements Comparable<FormatVersion> {

	protected final int mMajor;
	protected final int mMinor;

	public FormatVersion() {
		this(0, 0);
	}

	public FormatVersion(final int major, final int minor) {
		validateVersionNumber(major < 0, "Major number of FormatVersion cannot be negative!");
		validateVersionNumber(minor < 0, "Minor number of FormatVersion cannot be negative!");

		mMajor = major;
		mMinor = minor;
	}

	public static FormatVersion fromString(final String string) {
		final String[] split = string.split("\\.");
		if (split.length != 2) {
			return null;
		}
		try {
			return new FormatVersion(Integer.parseInt(split[0]), Integer.parseInt(split[1]));
		} catch (final NumberFormatException e) {
			return null;
		}
	}

	private static void validateVersionNumber(final boolean invalidExpression, final String exceptionMsg) {
		if (invalidExpression) {
			throw new IllegalArgumentException(exceptionMsg);
		}
	}

	public int getMajor() {
		return mMajor;
	}

	public int getMinor() {
		return mMinor;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}

		if (obj instanceof FormatVersion) {
			final FormatVersion other = FormatVersion.class.cast(obj);
			if (this.compareTo(other) == 0) {
				return true;
			}
		}

		return false;
	}

	@Override
	public int compareTo(FormatVersion other) {
		final int compareMajorResult = Integer.compare(this.getMajor(), other.getMajor());

		if (compareMajorResult == 0) {
			// Major number of both objects are equal
			// Compare minor numbers and return compare result
			return Integer.compare(this.getMinor(), other.getMinor());
		} else {
			// Major number of both objects are not equal
			// Return compare result of major numbers
			return compareMajorResult;
		}
	}

	@Override
	public String toString() {
		return mMajor + "." + mMinor;
	}
}
