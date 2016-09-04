/*
 * Copyright (C) 2014-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.option;

import java.io.IOException;

import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

public class LoggerOption extends Option {

	private String mDefaultDest;
	private final LogProxy mLogger;

	public LoggerOption(String description, LogProxy logger) {
		super(true, description);
		mDefaultDest = logger.getDestination();
		mLogger = logger;
	}
	
	private final void changeLoggerDest(String newdest) {
		try {
			mLogger.changeDestination(String.valueOf(newdest));
		} catch (final IOException eio) {
			throw new SMTLIBException("Could not change logging destination",
					eio);
		}
	}

	@Override
	public void set(Object value) {
		if (value instanceof QuotedObject) {
			value = ((QuotedObject) value).getValue();
		}
		if (mLogger.canChangeDestination()) {
			changeLoggerDest(String.valueOf(value));
		} else {
			mLogger.warn("Attempt to change the destionation of the logger which cannot change its destination!");
		}
	}

	@Override
	public Object get() {
		return new QuotedObject(mLogger.getDestination());
	}

	@Override
	public void reset() {
		if (mLogger.canChangeDestination()) {
			changeLoggerDest(mDefaultDest);
		}
	}

	@Override
	public Object defaultValue() {
		return mDefaultDest;
	}

	@Override
	public Option copy() {
		return this; // cannot copy this option since I cannot copy the logger!
	}

	@Override
	public void started() {
		mDefaultDest = mLogger.getDestination();
	}

}
