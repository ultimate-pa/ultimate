package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

public class AbstractVariable {
	private final String mIdentifier;

	public AbstractVariable(String str) {
		mIdentifier = str;
	}

	public String getString() {
		return mIdentifier;
	}

	@Override
	public String toString() {
		return mIdentifier.toString();
	}
	
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mIdentifier == null) ? 0 : mIdentifier.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		AbstractVariable other = (AbstractVariable) obj;
		if (mIdentifier == null) {
			if (other.mIdentifier != null)
				return false;
		} else if (!mIdentifier.equals(other.mIdentifier))
			return false;
		return true;
	}

}
