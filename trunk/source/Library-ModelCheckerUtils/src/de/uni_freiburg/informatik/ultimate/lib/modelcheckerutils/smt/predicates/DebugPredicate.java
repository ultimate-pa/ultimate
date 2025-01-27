/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramFunction;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class DebugPredicate implements IPredicate {

	private final String mDebugMessage;
	private final int mSerialNumber;
	private final Term mTerm;

	public DebugPredicate(final String debugMessage, final int serialNumber, final Term dontCareTerm) {
		mDebugMessage = debugMessage;
		mSerialNumber = serialNumber;
		mTerm = dontCareTerm;
	}

	@Override
	public Term getFormula() {
		return mTerm;
	}

	@Override
	public Term getClosedFormula() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<IProgramVar> getVars() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<IProgramFunction> getFuns() {
		throw new UnsupportedOperationException();
	}

	public String getDebugMessage() {
		return mDebugMessage;
	}

	@Override
	public String toString() {
		return mDebugMessage;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, mSerialNumber);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj instanceof final DebugPredicate other && mSerialNumber == other.mSerialNumber) {
			// Different predicates with the same serial number must not be used within the same context.
			// Hence we throw an exception if they are compared for equality.
			// The only case in which two DebugPredicate are considered equal is reference equality (case 1 above).
			//
			// This aligns with the implementation in BasicPredicate and UnknownState.
			throw new UnsupportedOperationException("different predicates with same serial number");
		}
		return false;
	}

}
