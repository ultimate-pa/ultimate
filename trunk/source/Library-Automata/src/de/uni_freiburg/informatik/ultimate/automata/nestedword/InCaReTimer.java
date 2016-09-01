/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

/**
 * Encapsulates three stopwatches, one for internal, one for call, and one for return transitions.
 * Only one stopwatch may run at the same time.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class InCaReTimer {
	
	private long mInternal;
	private long mCall;
	private long mReturn;
	
	private long mStartTime;
	
	/**
	 * Constructor.
	 */
	public InCaReTimer() {
		mInternal = 0;
		mCall = 0;
		mReturn = 0;
		mStartTime = 0;
	}
	
	private void run() {
		assert mStartTime == 0 : "timer already running";
		mStartTime = System.nanoTime();
	}
	
	/**
	 * Runs internal stopwatch.
	 */
	public void runIn() {
		run();
	}
	
	/**
	 * Runs call stopwatch.
	 */
	public void runCa() {
		run();
	}
	
	/**
	 * Runs return stopwatch.
	 */
	public void runRe() {
		run();
	}
	
	/**
	 * Stops internal stopwatch.
	 */
	public void stopIn() {
		mInternal += (System.nanoTime() - mStartTime);
		mStartTime = 0;
	}
	
	/**
	 * Stops call stopwatch.
	 */
	public void stopCa() {
		mCall += (System.nanoTime() - mStartTime);
		mStartTime = 0;
	}
	
	/**
	 * Stops return stopwatch.
	 */
	public void stopRe() {
		mReturn += (System.nanoTime() - mStartTime);
		mStartTime = 0;
	}
	
	public long getInternal() {
		return mInternal;
	}
	
	public long getCall() {
		return mCall;
	}
	
	public long getReturn() {
		return mReturn;
	}
	
	/**
	 * Pretty-prints nano seconds in seconds.
	 * 
	 * @param time
	 *            time in nano seconds
	 * @return pretty-printed time
	 */
	public static String prettyprintNanoseconds(final long time) {
		final long seconds = time / 1_000_000_000;
		final long tenthDigit = (time / 100_000_000) % 10;
		return Long.toString(seconds) + '.' + Long.toString(tenthDigit) + 's';
	}
	
	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		// @formatter:off
		builder.append(prettyprintNanoseconds(mInternal))
				.append("In")
				.append(prettyprintNanoseconds(mCall))
				.append("Ca")
				.append(prettyprintNanoseconds(mReturn))
				.append("Re");
		// @formatter:on
		return builder.toString();
	}
}
