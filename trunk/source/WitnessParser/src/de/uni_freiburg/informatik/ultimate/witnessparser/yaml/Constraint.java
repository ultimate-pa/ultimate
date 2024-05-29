package de.uni_freiburg.informatik.ultimate.witnessparser.yaml;

/**
 * The Constraint of a Waypoint gives the requirement for the Waypoint and is not allowed for every type. For Waypoint
 * types which don't have a constraint format or value null is returned instead.
 *
 * @author Helen Meyer (helen.anna.meyer@gmail.com)
 */
public class Constraint {
	private final String mValue;
	private final String mFormat;

	public Constraint(final String value, final String format) {
		mValue = value;
		mFormat = format;
	}

	public String getValue() {
		return mValue;
	}

	public String getFormat() {
		return mFormat;
	}

	@Override
	public String toString() {
		// maybe change to not print "null" if one of them is null?
		return "(" + mValue + ", " + mFormat + ")";
	}
}
