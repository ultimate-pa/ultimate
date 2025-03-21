/*
 * Copyright (C) 2009-2012 Juergen Christ
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of the ULTIMATE SmtLibUtils Library.
 *
 * The ULTIMATE SmtLibUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SmtLibUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SmtLibUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SmtLibUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SmtLibUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils;

import java.text.FieldPosition;
import java.text.Format;
import java.text.MessageFormat;
import java.text.ParsePosition;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Class used to prevent unnecessary String conversions and concatenations.
 *
 * Just use {num} to refer to the array position like in
 * <code>new DebugMessage("Arg 1 is {1} and 0 is {0}",obj0,obj1)</code>. The string is formatted by
 * {@link java.text.MessageFormat}.
 *
 * @author Juergen Christ
 */
public class DebugMessage {
	private static class TermDirectFormat extends Format {

		private static final long serialVersionUID = -6518060753837104534L;

		@Override
		public StringBuffer format(final Object obj, final StringBuffer toAppendTo, final FieldPosition pos) {
			return toAppendTo.append(((Term) obj).toStringDirect());
		}

		@Override
		public Object parseObject(final String source, final ParsePosition pos) {
			throw new UnsupportedOperationException();
		}

	}

	private static final TermDirectFormat TERM_FORMAT = new TermDirectFormat();
	private final boolean mTermDirect;
	private final String mMsg;
	private final Object[] mParams;

	public DebugMessage(final String msg, final Object... params) {
		this(false, msg, params);
	}

	public DebugMessage(final boolean termDirect, final String msg, final Object... params) {
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
