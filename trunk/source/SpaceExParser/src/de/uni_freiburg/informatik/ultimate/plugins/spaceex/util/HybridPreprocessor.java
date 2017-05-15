/*
 * Copyright (C) 2016 Julian Loeffler (loefflju@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE SpaceExParser plug-in.
 *
 * The ULTIMATE SpaceExParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE SpaceExParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE SpaceExParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE SpaceExParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE SpaceExParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

import java.util.ArrayList;
import java.util.List;

public class HybridPreprocessor {

	// update of the form x := x+1 becomes x := (x+1)
	// needed for postfix form to ensure precedence.
	public static List<String> preprocessForUpdate(final List<String> infixArray) {
		final List<String> res = new ArrayList<>();
		boolean open = false;
		for (final String el : infixArray) {
			if ("==".equals(el)) {
				res.add(el);
				res.add("(");
				open = true;
			} else if ("&".equals(el)) {
				if (open) {
					res.add(")");
					open = false;
				}
				res.add(el);
			} else {
				res.add(el);
			}
		}
		if (open) {
			res.add(")");
		}
		return res;
	}

	public static List<String> preprocessForTermBuilding(final List<String> postfix) {
		final List<String> newPostfix = new ArrayList<>();
		for (String el : postfix) {
			// & is "and" in SMT
			// == is "=" in SMT
			// | is "or" in SMT
			if ("&".equals(el) || "&&".equals(el)) {
				el = "and";
			} else if ("==".equals(el) || ":=".equals(el)) {
				el = "=";
			} else if ("|".equals(el) || "||".equals(el)) {
				el = "or";
			}
			newPostfix.add(el);
		}
		return newPostfix;
	}

	public static String preprocessStatement(final String statement) {
		if (statement == null) {
			return "";
		}
		String st = statement.replaceAll(":=", "==");
		st = st.replaceAll("&&", "&");
		st = st.replaceAll("\\|\\|", "|");
		st = st.replaceAll("'", "");
		return st;
	}
}
