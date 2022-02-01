package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences;

public enum EnableWhen {

	ALWAYS("Enabled"),
	NEVER("Disabled"),
	ONLY_FOR_CONCURRENT_PROGRAMS("Enabled iff program contains a fork statement"),
	ONLY_FOR_SEQUENTIAL_PROGRAMS("Enabled iff program contains no fork statement");

	private final String mDescription;

	private EnableWhen(final String displayName) {
		mDescription = displayName;
	}

	public String getDescription() {
		return mDescription;
	}
	
	public boolean isEnabled(final boolean programIsConcurrent) {
		switch (this) {
		case ALWAYS:
			return true;
		case NEVER:
			return false;
		case ONLY_FOR_CONCURRENT_PROGRAMS:
			return programIsConcurrent;
		case ONLY_FOR_SEQUENTIAL_PROGRAMS:
			return !programIsConcurrent;
		}
		throw new IllegalStateException("This enum object has an unknown state: " + this);
	}
	
}
