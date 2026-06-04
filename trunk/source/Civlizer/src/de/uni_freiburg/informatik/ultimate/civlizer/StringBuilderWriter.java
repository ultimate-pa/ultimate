/*
 * Copyright (C) 2026 Dominik Klumpp (klumpp@lix.polytechnique.fr)
 * Copyright (C) 2026 École Polytechnique
 *
 * This file is part of the ULTIMATE Civlizer plug-in.
 *
 * The ULTIMATE Civlizer plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Civlizer plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Civlizer plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Civlizer plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Civlizer plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

/**
 * A {@link PrintWriter} that writes output both to an underlying writer and to an internal {@link StringBuilder}.
 *
 * <p>
 * This class is used to capture generated output as a string while simultaneously forwarding it to a backing writer.
 * </p>
 */
final class StringBuilderWriter extends PrintWriter {

	private final StringBuilder mResult;

	StringBuilderWriter() throws IOException {
		super(new FileWriter("/tmp/temporary.bpl")); // to be change TODO
		mResult = new StringBuilder();
	}

	StringBuilder getResult() {
		return mResult;
	}

	@Override
	public String toString() {
		return mResult.toString();
	}

	@Override
	public void print(final String s) {
		super.print(s);
		mResult.append(s);
	}

	@Override
	public void println(final String s) {
		super.println(s);
		mResult.append(s).append("\n");
	}
}