/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.Map.Entry;
import java.util.Scanner;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class LineDirectiveMapping {
	private final TreeMap<Integer, Pair<Integer, String>> mMapping;

	public LineDirectiveMapping(final String file) {
		super();
		mMapping = constructLineDirectiveMapping(file);
	}

	/**
	 * @return A map whose domain are all lines of the input file in which there is a #line directive. Each such line
	 *         number is mapped to a pair. The first entry of this pair is the line number which is mentioned in the
	 *         #line directive, the second entry is the filename which is mentioned in the #line directive or null if no
	 *         filename is mentioned.
	 */
	private static TreeMap<Integer, Pair<Integer, String>> constructLineDirectiveMapping(final String file) {
		final TreeMap<Integer, Pair<Integer, String>> result = new TreeMap<>();
		final Scanner scanner = new Scanner(file);
		int currentLine = 0;
		while (scanner.hasNextLine()) {
			final String line = scanner.nextLine();
			currentLine++;
			{
				final int idx = line.lastIndexOf("#line");
				if (idx == -1) {
					continue;
				}
				int curcol = idx + 5;
				while (curcol < line.length() && Character.isWhitespace(line.charAt(curcol))) {
					curcol++;
				}
				final int fstDigit = curcol;
				while (curcol < line.length() && Character.isDigit(line.charAt(curcol))) {
					curcol++;
				}
				final String digitSequence = line.substring(fstDigit, curcol);
				while (curcol < line.length() && Character.isWhitespace(line.charAt(curcol))) {
					curcol++;
				}
				String filename;
				if (curcol < line.length() && line.charAt(curcol) == '\"') {
					curcol++;
					final int fstfn = curcol;
					while (line.charAt(curcol) != '\"') {
						curcol++;
					}
					filename = line.substring(fstfn, curcol);

				} else {
					filename = null;
				}
				result.put(currentLine, new Pair<>(Integer.parseInt(digitSequence), filename));
			}
		}
		scanner.close();
		return result;
	}

	/**
	 *
	 * @param lineInTu
	 * @param filename
	 * @return
	 */
	public Pair<Integer, String> getOriginal(final int lineInTu, final String filename) {
		final Entry<Integer, Pair<Integer, String>> floor = mMapping.floorEntry(lineInTu);
		if (floor == null) {
			return new Pair<>(lineInTu, filename);
		}
		final int distanceToLastLineDirective = (lineInTu - floor.getKey());
		return new Pair<>(floor.getValue().getFirst() + distanceToLastLineDirective, floor.getValue().getSecond());
	}

}
