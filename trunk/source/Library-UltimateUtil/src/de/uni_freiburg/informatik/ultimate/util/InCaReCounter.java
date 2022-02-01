/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

/**
 * Three counters, one for internal, one for call, one for return.
 * 
 * @author Matthias Heizmann
 *
 */
public class InCaReCounter {
	private static final boolean mToStringIsSum = true;
	private int mInternal;
	private int mCall;
	private int mReturn;

	public InCaReCounter() {
		super();
		mInternal = 0;
		mCall = 0;
		mReturn = 0;
	}

	public int getInternal() {
		return mInternal;
	}

	public int getCall() {
		return mCall;
	}

	public int getReturn() {
		return mReturn;
	}

	public void incIn() {
		mInternal++;
	}

	public void incCa() {
		mCall++;
	}

	public void incRe() {
		mReturn++;
	}

	@Override
	public String toString() {
		if (mToStringIsSum) {
			return String.valueOf(mInternal + mCall + mReturn);
		}
		return mInternal + "In " + mCall + "Ca " + mReturn + "Re";
	}

	/**
	 * Add all values of another counter to the values of this counter.
	 */
	public void add(final InCaReCounter inCaReCounter) {
		mInternal += inCaReCounter.getInternal();
		mCall += inCaReCounter.getCall();
		mReturn += inCaReCounter.getReturn();
	}

	/**
	 * @return sum of all three counters
	 */
	public int getSum() {
		return getInternal() + getCall() + getReturn();
	}

}
