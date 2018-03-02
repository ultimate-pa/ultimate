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
package de.uni_freiburg.informatik.ultimate.smtinterpol.option;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;

/**
 * The <code>:verbosity</code> option.  This option is specialized to directly
 * modify the {@link LogProxy} to set the correct value.
 * 
 * For backward compatibility the interface methods return a BigInteger.
 * @author Juergen Christ
 */
public class VerbosityOption extends Option {

	private int mDefaultLvl;
	private final LogProxy mLogger;

	public VerbosityOption(LogProxy logger) {
		super(true, "How much output to produce on the diagnostic output "
				+ "channel.  The bigger the number the more output will be produces.  0 "
				+ "turns off diagnostic output.");
		mLogger = logger;
		mDefaultLvl = mLogger.getLoglevel();
	}
	@Override
	public Option copy() {
		return this; // Cannot copy verbosity option.  Does not make sense!
	}
	@Override
	public void set(Object value) {
		int lvl;
		if (value instanceof Number) {
			lvl = ((Number) value).intValue();
		} else if (value instanceof String) {
			try {
				lvl = Integer.parseInt((String) value);
			} catch (final NumberFormatException enfe) {
				throw new SMTLIBException("Not a valid number: " + value);
			}
		} else {
			throw new SMTLIBException("Not a valid number: " + value);
		}
		// Normalize value
		if (lvl < LogProxy.LOGLEVEL_OFF) {
			lvl = LogProxy.LOGLEVEL_OFF;
		} else if (lvl > LogProxy.LOGLEVEL_TRACE) {
			lvl = LogProxy.LOGLEVEL_TRACE;
		}
		mLogger.setLoglevel(lvl);
	}

	@Override
	public Object get() {
		return BigInteger.valueOf(mLogger.getLoglevel());
	}

	@Override
	public void reset() {
		mLogger.setLoglevel(mDefaultLvl);
	}

	@Override
	public Object defaultValue() {
		return BigInteger.valueOf(mDefaultLvl);
	}
	@Override
	public void started() {
		mDefaultLvl = mLogger.getLoglevel();
	}

}
