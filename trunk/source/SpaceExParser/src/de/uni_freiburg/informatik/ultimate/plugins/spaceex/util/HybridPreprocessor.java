package de.uni_freiburg.informatik.ultimate.plugins.spaceex.util;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.spaceex.parser.preferences.SpaceExPreferenceManager;

public class HybridPreprocessor {
	SpaceExPreferenceManager mPreferencemanager;
	
	// update of the form x := x+1 becomes x := (x+1)
	// needed for postfix form.
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
			open = false;
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
