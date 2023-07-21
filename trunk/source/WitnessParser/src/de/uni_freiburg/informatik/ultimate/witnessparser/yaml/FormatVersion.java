package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

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
		final String[] split = string.split(".");
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
