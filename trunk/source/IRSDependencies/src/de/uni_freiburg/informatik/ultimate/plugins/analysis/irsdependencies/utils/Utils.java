/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.utils;

import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

public class Utils {
	public static String insertLineBreaks(final int chopSize, String s) {
		if (s.length() < chopSize) {
			return s;
		} else {
			int chops = s.length() / chopSize;
			int currentChopSize = chopSize;
			int possibleChopPoint = 0;
			int oldPossibleChopPoint = 0;
			while (chops > 0) {

				possibleChopPoint = s.indexOf(';', oldPossibleChopPoint);
				if (possibleChopPoint > currentChopSize) {
					s = s.substring(0, oldPossibleChopPoint).concat("\n")
							.concat(s.substring(oldPossibleChopPoint));
					--chops;
					currentChopSize = currentChopSize + chopSize;
				}
				oldPossibleChopPoint = possibleChopPoint + 1;

				if (possibleChopPoint > s.length() || possibleChopPoint == -1) {
					break;
				}

			}
			return "\n" + s;
		}

	}

	public static String traceToString(final List<IcfgEdge> trace) {
		final StringBuilder sb = new StringBuilder();
		for (final IcfgEdge edge : trace) {
			sb.append(edgeToString(edge));
			sb.append(" ");
		}
		return sb.toString();
	}

	public static String edgeToString(final IcfgEdge edge) {
		if (edge instanceof CodeBlock) {
			return ((CodeBlock) edge).getPrettyPrintedStatements();
		} else {
			return edge.toString();
		}
	}

	public static <T> HashSet<T> intersect(final HashSet<T> a, final HashSet<T> b) {
		final HashSet<T> rtr = new HashSet<>();
		for (final T element : a) {
			if (b.contains(element)) {
				rtr.add(element);
			}
		}
		return rtr;
	}

}
