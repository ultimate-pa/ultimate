/*
 * Copyright (C) 2009-2012 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.util;

import java.text.FieldPosition;
import java.text.Format;
import java.text.MessageFormat;
import java.text.ParsePosition;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Class used to prevent unnecessary String conversions and 
 * concatenations.
 * 
 * Just use {num} to refer to the array position like in
 * <code>new DebugMessage("Arg 1 is {1} and 0 is {0}",obj0,obj1)</code>.
 * The string is formatted by {@link java.text.MessageFormat}.
 * 
 * @author Juergen Christ
 */
public class DebugMessage {
	private static class TermDirectFormat extends Format {

		private static final long serialVersionUID = -6518060753837104534L;

		@Override
		public StringBuffer format(Object obj, StringBuffer toAppendTo,
				FieldPosition pos) {
			return toAppendTo.append(((Term)obj).toStringDirect());
		}

		@Override
		public Object parseObject(String source, ParsePosition pos) {
			throw new UnsupportedOperationException();
		}
		
	}
	private static final TermDirectFormat TERM_FORMAT = new TermDirectFormat();
	private final boolean mTermDirect;
	private final String mMsg;
	private final Object[] mParams;
	public DebugMessage(String msg, Object... params) {
		this(false, msg, params);
	}
	public DebugMessage(boolean termDirect, String msg, Object... params) {
		mTermDirect = termDirect;
		mMsg = msg;
		mParams = params;
	}
	@Override
	public String toString() {
		final MessageFormat mf = new MessageFormat(mMsg);
		if (mTermDirect) {
			for (int i = 0; i < mParams.length; ++i) {
				if (mParams[i] instanceof Term) {
					mf.setFormatByArgumentIndex(i, TERM_FORMAT);
				}
			}
		}
		return mf.format(mParams, new StringBuffer(), null).toString();
	}
}
