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
package de.uni_freiburg.informatik.ultimate.smtinterpol;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;

public final class ChannelUtil {
	private ChannelUtil() {
		// hide constructor
	}
	public static PrintWriter createChannel(String file) throws IOException {
		if ("stdout".equals(file)) {
			return new PrintWriter(System.out);
		}
		if ("stderr".equals(file)) {
			return new PrintWriter(System.err);
		} else {
			return new PrintWriter(new FileWriter(file));
		}
	}
}
