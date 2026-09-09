/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps;

/**
 * Different modes for the source-to-source translation of IDPs.
 *
 * <ul>
 * <li>{@link #NONE}: Disable interrupt translation.</li>
 * <li>{@link #ONE_THREAD_PER_ISR}: Introduce one thread for each ISR, that calls the corresponding ISR infinitely
 * often.</li>
 * <li>{@link #ALL_ISR_IN_ONE_THREAD}: Introduce only one thread that calls all ISRs non-deterministically in an
 * infinite loop.</li>
 * <li>{@link #ONE_THREAD_PER_ISR_FORK_JOIN}: Introduce one thread for each ISR, that calls the corresponding ISR
 * infinitely often, but only fork the ISR thread if the interrupt is enabled and join it otherwise.</li>
 * </ul>
 */
public enum InterruptTranslationMode {

	/**
	 * Disable interrupt translation.
	 */
	NONE(0, "No interrupt translation"),

	/**
	 * Introduce one thread for each ISR, that calls the corresponding ISR infinitely often.
	 */
	ONE_THREAD_PER_ISR(1, "One thread per ISR"),

	/**
	 * Introduce only one thread that calls all ISRs non-deterministically in an infinite loop.
	 */
	ALL_ISR_IN_ONE_THREAD(2, "One thread for all ISRs"),

	/**
	 * Introduce one thread for each ISR, that calls the corresponding ISR infinitely often, but only fork the ISR
	 * thread if the interrupt is enabled and join it otherwise.
	 */
	ONE_THREAD_PER_ISR_FORK_JOIN(3, "One thread per ISR with fork-join");

	final int mNum;
	final String mDesc;

	InterruptTranslationMode(final int num, final String desc) {
		mNum = num;
		mDesc = desc;
	}

	public int getNum() {
		return mNum;
	}

	public String getDesc() {
		return mDesc;
	}

}
