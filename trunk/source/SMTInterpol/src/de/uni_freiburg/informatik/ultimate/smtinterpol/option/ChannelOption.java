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

import java.io.IOException;
import java.io.PrintWriter;

import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.smtinterpol.ChannelUtil;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;

/**
 * An option specialized for output channels.  This option supports strings to
 * describe the channels according to SMTLIB specifications, i.e., either file
 * names, "stdout", or "stderr".  This option is designed to be usable either
 * for direct storage of a PrintWriter or a wrapped PrintWriter used, e.g., by
 * a {@link DefaultLogger}. 
 * @author Juergen Christ.
 *
 */
public class ChannelOption extends Option {

	private String mName;
	private String mDefaultName;
	private PrintWriter mWriter;

	public ChannelOption(String defaultChannel,
			boolean onlineModifiable, String description) {
		super(onlineModifiable, description);
		createChannel(defaultChannel);
		mName = mDefaultName = defaultChannel;
	}
	@Override
	public Option copy() {
		return this; // Cannot copy channel option.  Does not make sense!
	}
	@Override
	public void set(Object value) {
		if (value instanceof QuotedObject) {
			value = ((QuotedObject) value).getValue();
		}
		final String val = value.toString();
		createChannel(val);
		mName = val;
	}

	@Override
	public Object get() {
		return new QuotedObject(mName);
	}

	@Override
	public void reset() {
		createChannel(mName);
		mName = mDefaultName;
	}

	@Override
	public Object defaultValue() {
		return new QuotedObject(mDefaultName);
	}
	
	private void createChannel(String file) {
		try {
			mWriter = ChannelUtil.createChannel(file);
		} catch (final IOException eIO) {
			throw new SMTLIBException(eIO);
		}
	}
	@Override
	public void started() {
		mDefaultName = mName;
	}
	public PrintWriter getChannel() {
		return mWriter;
	}

}
