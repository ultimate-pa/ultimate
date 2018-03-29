package de.uni_freiburg.informatik.ultimate.lib.srparse;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;

public abstract class SrParseScope {

	private final CDD mCdd1;
	private final CDD mCdd2;

	protected SrParseScope(final CDD cdd1, final CDD cdd2) {
		mCdd1 = cdd1;
		mCdd2 = cdd2;
	}

	public CDD getCdd1() {
		return mCdd1;
	}

	public CDD getCdd2() {
		return mCdd2;
	}

	@Override
	public abstract String toString();

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mCdd1 == null) ? 0 : mCdd1.hashCode());
		result = prime * result + ((mCdd2 == null) ? 0 : mCdd2.hashCode());
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
		final SrParseScope other = (SrParseScope) obj;
		if (mCdd1 == null) {
			if (other.mCdd1 != null) {
				return false;
			}
		} else if (!mCdd1.equals(other.mCdd1)) {
			return false;
		}
		if (mCdd2 == null) {
			if (other.mCdd2 != null) {
				return false;
			}
		} else if (!mCdd2.equals(other.mCdd2)) {
			return false;
		}
		return true;
	}
}
