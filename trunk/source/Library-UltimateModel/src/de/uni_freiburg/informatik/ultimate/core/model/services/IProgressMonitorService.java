/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IProgressMonitorService extends IProgressAwareTimer, IToolchainCancel {

	/**
	 * Name the currently running task s.t. a user may see the name.
	 *
	 * @param task
	 *            A name that will be displayed to the user.
	 */
	void setSubtask(final String task);

	/**
	 * <b>Note: This changes the state of this object</b>
	 * <p>
	 * Set a time limit after which this monitor signals timeout.
	 *
	 * A convenient way of setting this deadline is using System.currentTimeMillis() + time limit (in ms) as value.
	 *
	 * This will remove all child timers and only the newly set deadline will be respected. This deadline will also be
	 * the root deadline.
	 * </p>
	 *
	 * @param date
	 *            A date in the future (the difference, measured in milliseconds, between the current time and midnight,
	 *            January 1, 1970 UTC) after which a running toolchain should be stopped. Must be non-negative or -1 to
	 *            disable the deadline.
	 */
	void setDeadline(final long date);

	/**
	 * Creates a {@link IUltimateServiceProvider} instance with a different timer for sub-timeouts. The new
	 * {@link IUltimateServiceProvider} instance will have a {@link IProgressMonitorService} with the timeout specified
	 * by the supplied {@link IProgressAwareTimer}.
	 *
	 * @param services
	 *            The current {@link IUltimateServiceProvider} instance.
	 * @param timer
	 *            The new {@link IP<rogressAwareTimer}
	 *
	 * @return An {@link IUltimateServiceProvider} instance that is identical to <code>services</code> except that its
	 *         {@link IProgressMonitorService} instance will timeout when <code>timer</code> timeouts OR when the old
	 *         {@link IProgressMonitorService} timeouts.
	 */
	IUltimateServiceProvider registerChildTimer(final IUltimateServiceProvider services,
			final IProgressAwareTimer timer);
}
