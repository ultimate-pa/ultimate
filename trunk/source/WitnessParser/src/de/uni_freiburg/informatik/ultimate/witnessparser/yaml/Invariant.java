package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

public class Invariant {

	private final String mExpression;
	private final String mType;
	private final String mFormat;

	public Invariant(final String expression, final String type, final String format) {
		mExpression = expression;
		mType = type;
		mFormat = format;
	}

	public String getExpression() {
		return mExpression;
	}

	public String getType() {
		return mType;
	}

	public String getFormat() {
		return mFormat;
	}

	@Override
	public String toString() {
		return mExpression + " [" + mType + ", " + mFormat + "]";
	}
}
