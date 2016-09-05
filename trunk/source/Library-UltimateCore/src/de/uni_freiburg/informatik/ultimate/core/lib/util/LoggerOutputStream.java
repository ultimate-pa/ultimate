/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.core.lib.util;

import java.io.OutputStream;
import java.nio.charset.Charset;
import java.util.function.Consumer;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * {@link LoggerOutputStream} is a wrapper for any consumer (especially an ILogger instance) s.t. it can be used as
 * OutputStream, e.g. in a PrintWriter.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class LoggerOutputStream extends OutputStream {

	private final Consumer<String> mLinePrinter;
	private static final String LINE_BREAK = CoreUtil.getPlatformLineSeparator();

	private StringBuilder mLineBuffer;

	/**
	 * Create a {@link LoggerOutputStream} instance that wraps a consumer such that it can be used as an
	 * {@link OutputStream}.
	 * 
	 * @param linePrinter
	 *            The {@link Consumer} function that gets called whenever a line has to be printed.
	 */
	public LoggerOutputStream(final Consumer<String> linePrinter) {
		mLinePrinter = linePrinter;
		mLineBuffer = new StringBuilder();
	}

	@Override
	public void write(final int b) {
		mLineBuffer.append(new String(new byte[] { (byte) (b & 0xff) }, Charset.defaultCharset()));

		final int length = mLineBuffer.length();
		final int lastIndex = length - LINE_BREAK.length();
		if (lastIndex <= 0) {
			return;
		}
		if (LINE_BREAK.equals(mLineBuffer.substring(lastIndex))) {
			mLineBuffer.delete(lastIndex, length);
			flush();
		}
	}

	@Override
	public void flush() {
		mLinePrinter.accept(mLineBuffer.toString());
		mLineBuffer = new StringBuilder();
	}
}
