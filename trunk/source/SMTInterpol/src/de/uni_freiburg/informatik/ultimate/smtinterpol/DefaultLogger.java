/*
 * Copyright (C) 2014 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.io.IOException;
import java.io.PrintWriter;
import java.util.Formatter;

public class DefaultLogger implements LogProxy {

	// Multithreading support
	private static final Object LOCK = new Object();
	
	// Loglevel strings
	private static final String[] LEVELS = {
		"FATAL",
		"ERROR",
		"WARN",
		"INFO",
		"DEBUG",
		"TRACE"
	};

	private PrintWriter mWriter = new PrintWriter(System.err);
	private Formatter mFormat = new Formatter(mWriter);
	private String mDest = "stderr";
	
	private int mLevel = Config.DEFAULT_LOG_LEVEL;
	
	@Override
	public void setLoglevel(int level) {
		mLevel = level;
	}

	@Override
	public int getLoglevel() {
		return mLevel;
	}

	private final boolean isEnabled(int lvl) {
		return lvl <= mLevel;
	}
	
	private final void log(int lvl, Object msg) {
		synchronized (LOCK) {
			mWriter.print(LEVELS[lvl - 1]);
			mWriter.print(" - ");
			mWriter.println(msg);
			mWriter.flush();
		}
	}
	
	private final void log(int lvl, String msg, Object[] params) {
		if (params.length == 0) {
			log(lvl, msg);
		}
		synchronized (LOCK) {
			mWriter.print(LEVELS[lvl - 1]);
			mWriter.print(" - ");
			mFormat.format(msg, params);
			mWriter.println();
			mWriter.flush();
		}
	}
	
	@Override
	public boolean isFatalEnabled() {
		return isEnabled(LOGLEVEL_FATAL);
	}

	@Override
	public void fatal(String msg, Object... params) {
		if (isFatalEnabled()) {
			log(LOGLEVEL_FATAL, msg, params);
		}
	}

	@Override
	public void fatal(Object msg) {
		if (isFatalEnabled()) {
			log(LOGLEVEL_FATAL, msg);
		}
	}

	@Override
	public void outOfMemory(String msg) {
		if (isFatalEnabled()) {
			log(LOGLEVEL_FATAL, msg);
		}
	}

	@Override
	public boolean isErrorEnabled() {
		return isEnabled(LOGLEVEL_ERROR);
	}

	@Override
	public void error(String msg, Object... params) {
		if (isErrorEnabled()) {
			log(LOGLEVEL_ERROR, msg, params);
		}
	}

	@Override
	public void error(Object msg) {
		if (isErrorEnabled()) {
			log(LOGLEVEL_ERROR, msg);
		}
	}

	@Override
	public boolean isWarnEnabled() {
		return isEnabled(LOGLEVEL_WARN);
	}

	@Override
	public void warn(String msg, Object... params) {
		if (isWarnEnabled()) {
			log(LOGLEVEL_WARN, msg, params);
		}
	}

	@Override
	public void warn(Object msg) {
		if (isWarnEnabled()) {
			log(LOGLEVEL_WARN, msg);
		}
	}

	@Override
	public boolean isInfoEnabled() {
		return isEnabled(LOGLEVEL_INFO);
	}

	@Override
	public void info(String msg, Object... params) {
		if (isInfoEnabled()) {
			log(LOGLEVEL_INFO, msg, params);
		}
	}

	@Override
	public void info(Object msg) {
		if (isInfoEnabled()) {
			log(LOGLEVEL_INFO, msg);
		}
	}

	@Override
	public boolean isDebugEnabled() {
		return isEnabled(LOGLEVEL_DEBUG);
	}

	@Override
	public void debug(String msg, Object... params) {
		if (isDebugEnabled()) {
			log(LOGLEVEL_DEBUG, msg, params);
		}
	}

	@Override
	public void debug(Object msg) {
		if (isDebugEnabled()) {
			log(LOGLEVEL_DEBUG, msg);
		}
	}

	@Override
	public boolean isTraceEnabled() {
		return isEnabled(LOGLEVEL_TRACE);
	}

	@Override
	public void trace(String msg, Object... params) {
		if (isTraceEnabled()) {
			log(LOGLEVEL_TRACE, msg, params);
		}
	}

	@Override
	public void trace(Object msg) {
		if (isTraceEnabled()) {
			log(LOGLEVEL_TRACE, msg);
		}
	}

	@Override
	public boolean canChangeDestination() {
		return true;
	}

	@Override
	public void changeDestination(String newDest) throws IOException {
		mWriter = ChannelUtil.createChannel(newDest);
		mFormat = new Formatter(mWriter);
		mDest = newDest;
	}

	@Override
	public String getDestination() {
		return mDest;
	}

}
