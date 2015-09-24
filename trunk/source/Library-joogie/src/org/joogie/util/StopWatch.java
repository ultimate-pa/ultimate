/*
 * Joogie translates Java bytecode to the Boogie intermediate verification language
 * Copyright (C) 2011 Martin Schaef and Stephan Arlt
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */

package org.joogie.util;

/**
 * @author arlt
 */
public class StopWatch {

	/**
	 * Start Time
	 */
	private long startTime;

	/**
	 * Stop Time
	 */
	private long stopTime;

	/**
	 * Enabled or Disabled
	 */
	private boolean enabled;

	/**
	 * Returns a started instance of a stop watch
	 * 
	 * @return Stop watch
	 */
	public static StopWatch getInstanceAndStart() {
		StopWatch stopWatch = new StopWatch();
		stopWatch.start();
		return stopWatch;
	}

	/**
	 * Start stop watch
	 */
	public void start() {
		startTime = System.currentTimeMillis();
		enabled = true;
	}

	/**
	 * Stops the stop watch
	 * 
	 * @return Time
	 */
	public long stop() {
		if (!isEnabled())
			return 0;

		stopTime = System.currentTimeMillis();
		enabled = false;

		return getTime();
	}

	/**
	 * Returns the time
	 * 
	 * @return Time
	 */
	public long getTime() {
		if (isEnabled())
			return System.currentTimeMillis() - startTime;

		return stopTime - startTime;
	}

	/**
	 * Checks whether the stop watch is enabled
	 * 
	 * @return true = stop watch is enabled
	 */
	public boolean isEnabled() {
		return enabled;
	}

}
