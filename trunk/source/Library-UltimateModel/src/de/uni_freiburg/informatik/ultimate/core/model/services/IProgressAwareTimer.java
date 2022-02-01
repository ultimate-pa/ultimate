/*
 * Copyright (C) 2016-2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model.services;

/**
 * An object that allows you to create timeouts that trigger either if the parent timeout triggers or when the local
 * timeout triggers.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IProgressAwareTimer {

	/**
	 * @return false iff cancellation of Toolchain is requested or deadline is exceeded.
	 */
	boolean continueProcessing();

	/**
	 * Create a new timer that will expire after <code>timeout</code> milliseconds.
	 *
	 * If the parent timer expires or is canceled, this timer will also expire. This also means that if you specify a
	 * timeout larger than the parent timer, you could effectively use the parent timer.
	 *
	 * @param timeout
	 *            A timeout in milliseconds. Has to be larger than 0.
	 * @return A new timer.
	 */
	IProgressAwareTimer getChildTimer(final long timeout);

	/**
	 * Create a new timer that will expire after the specified <code>percentage</code> of the remaining time of the
	 * parent timer has been elapsed.
	 *
	 * @param percentage
	 *            A value > 0 and <= 1.0
	 * @return A new timer.
	 */
	IProgressAwareTimer getChildTimer(final double percentage);

	/**
	 * Create a new timer that will expire after <code>timeout</code> milliseconds.
	 *
	 * @param timeout
	 *            A timeout in milliseconds. Has to be larger than 0.
	 * @return A new timer.
	 */
	IProgressAwareTimer getTimer(final long timeout);

	/**
	 * @return The parent timer or null if there is no parent timer.
	 */
	IProgressAwareTimer getParent();

	/**
	 * @return a long value that should be interpreted as date (i.e., some point in time after midnight January 1 1970
	 *         UTC in milliseconds).
	 */
	long getDeadline();

}
