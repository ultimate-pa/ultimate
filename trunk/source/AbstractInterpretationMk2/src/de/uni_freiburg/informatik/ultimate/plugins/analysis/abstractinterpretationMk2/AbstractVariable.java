package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

public class AbstractVariable {
	private final String mIdentifier;

	public AbstractVariable(String str) {
		this.mIdentifier = str;
	}

	public String getString() {
		return mIdentifier;
	}

	@Override
	public int hashCode() {
		return mIdentifier.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null || !(obj instanceof AbstractVariable)) {
			return false;
		}
		AbstractVariable other = (AbstractVariable) obj;
		return mIdentifier.equals(other.mIdentifier);
	}

	@Override
	public String toString() {
		return mIdentifier.toString();
	}

}
