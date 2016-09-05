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

import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

public class StringOptionWithWarning extends StringOption {

	private final String mWarning;
	private final LogProxy mLogger;

	public StringOptionWithWarning(String defaultValue,
			boolean onlineModifiable, String description, String warning,
			LogProxy logger) {
		super(defaultValue, onlineModifiable, description);
		mWarning = warning;
		mLogger = logger;
	}

	@Override
	public void set(Object value) {
		super.set(value);
		mLogger.warn(mWarning);
	}

}
