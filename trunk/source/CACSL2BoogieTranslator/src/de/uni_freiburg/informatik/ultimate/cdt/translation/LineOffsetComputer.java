/*
 * Copyright (C) 2024 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.cdt.translation;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class LineOffsetComputer {
	private Map<Integer, Integer> mLineOffsets;
	private final String mFile;

	public LineOffsetComputer(final String file) {
		mFile = file;
	}

	private void computeLineOffsets() {
		if (mLineOffsets != null) {
			// Already computed
			return;
		}
		mLineOffsets = new HashMap<>();
		mLineOffsets.put(1, 0);
		int offset = 1;
		int line = 2;
		for (final char c : mFile.toCharArray()) {
			if (c == '\n') {
				mLineOffsets.put(line, offset);
				line++;
			}
			offset++;
		}
	}

	public int getOffset(final int line) {
		computeLineOffsets();
		final Integer res = mLineOffsets.get(line);
		if (res == null) {
			throw new UnsupportedOperationException("Unknown line " + line);
		}
		return res;
	}
}
