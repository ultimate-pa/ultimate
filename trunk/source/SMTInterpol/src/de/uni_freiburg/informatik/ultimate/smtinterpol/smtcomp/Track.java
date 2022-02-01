/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtcomp;

public enum Track {
	MAIN(false, false, null, null),
	APPLICATION(true, false, ":print-success", "true"),
	UNSAT_CORE(false, true, ":produce-unsat-cores", "true"),
	PROOF_GEN(false, false, ":produce-proofs", "true");
	Track(boolean ppAllowed, boolean namedAllowed, String io, String iov) {
		mPushPopAllowed = ppAllowed;
		mNamedAllowed = namedAllowed;
		mInitialOption = io;
		mInitialOptionValue = iov;
	}
	public boolean isPushPopAllowed() {
		return mPushPopAllowed;
	}
	public boolean isNamedAllowed() {
		return mNamedAllowed;
	}
	public boolean hasInitalOption() {
		return mInitialOption != null;
	}
	public String getInitialOption() {
		return mInitialOption;
	}
	public String getInitialOptionValue() {
		return mInitialOptionValue;
	}
	private boolean mPushPopAllowed;
	private boolean mNamedAllowed;
	private String mInitialOption;
	private String mInitialOptionValue;
}
