/*
 * Copyright (C) 2016 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.core.coreplugin.services;

import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public class Log4J2Wrapper implements ILogger {

	private final Logger mLogger;

	public Log4J2Wrapper(final Logger logger) {
		mLogger = logger;
	}

	Logger getBacking() {
		return mLogger;
	}

	@Override
	public boolean isFatalEnabled() {
		return Level.FATAL.isMoreSpecificThan(mLogger.getLevel());
	}

	@Override
	public boolean isErrorEnabled() {
		return Level.ERROR.isMoreSpecificThan(mLogger.getLevel());
	}

	@Override
	public boolean isWarnEnabled() {
		return Level.WARN.isMoreSpecificThan(mLogger.getLevel());
	}

	@Override
	public boolean isInfoEnabled() {
		return mLogger.isInfoEnabled();
	}

	@Override
	public boolean isDebugEnabled() {
		return mLogger.isDebugEnabled();
	}

	@Override
	public void fatal(final Object msg, final Throwable t) {
		mLogger.log(Level.FATAL, msg, t);
	}

	@Override
	public void fatal(final Object msg) {
		mLogger.log(Level.FATAL, msg);
	}

	@Override
	public void error(final Object msg, final Throwable t) {
		mLogger.log(Level.ERROR, msg, t);
	}

	@Override
	public void error(final Object msg) {
		mLogger.log(Level.ERROR, msg);
	}

	@Override
	public void warn(final Object msg) {
		mLogger.log(Level.WARN, msg);
	}

	@Override
	public void info(final Object msg) {
		mLogger.log(Level.INFO, msg);
	}

	@Override
	public void debug(final Object msg) {
		mLogger.log(Level.DEBUG, msg);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mLogger == null) ? 0 : mLogger.hashCode());
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
		final Log4J2Wrapper other = (Log4J2Wrapper) obj;
		if (mLogger == null) {
			if (other.mLogger != null) {
				return false;
			}
		} else if (!mLogger.equals(other.mLogger)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "[" + hashCode() + "][" + getBacking().getLevel() + "] " + getBacking().getName();
	}

}
