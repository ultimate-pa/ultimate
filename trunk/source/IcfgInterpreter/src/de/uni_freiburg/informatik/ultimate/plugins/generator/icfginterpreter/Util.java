package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;

public class Util {
	public static <T> ArrayList<T> copyList(final Collection<T> map) {
		final ArrayList<T> clone = new ArrayList<>(map);
		return clone;
	}

	public static <T, D> HashMap<T, D> copyMap(final Map<T, D> map) {
		final HashMap<T, D> clone = new HashMap<>(map);
		return clone;
	}

	public static <T> HashSet<T> copySet(final Set<T> set) {
		final HashSet<T> clone = new HashSet<>(set);
		return clone;
	}

	@SafeVarargs
	public static <T> ArrayList<T> toList(final T... terms) {
		return new ArrayList<>(Arrays.asList(terms));
	}

	public static <T> ArrayList<T> filter(final List<T> elements, final Predicate<T> isIncluded) {
		final ArrayList<T> out = new ArrayList<>();

		for (final T element : elements) {
			if (!isIncluded.test(element)) {
				continue;
			}
			out.add(element);
		}

		return out;
	}

	public static <T> HashSet<T> filter(final Set<T> elements, final Predicate<T> isIncluded) {
		final HashSet<T> out = new HashSet<>();

		for (final T element : elements) {
			if (!isIncluded.test(element)) {
				continue;
			}
			out.add(element);
		}

		return out;
	}

	/* Quantifier-free Arrays, Bit-Vectors, and integer maths */
	private final static Theory theory = new Theory(Logics.QF_AUFBVLIA);

	public static Theory getTheory() {
		return theory;
	}

	public static int compareBaseOrder(final ExecutionTerm a, final ExecutionTerm b) {
		return Integer.compare(a.hashCode(), b.hashCode());
	}

	public static String getIndent(final int depth) {
		return "  ".repeat(depth);
	}

	public static int SMTDiv(final int m, final int n) {
		final double div = ((double) m) / n;
		// n > 0, (div m n) = floor(m/n)
		if (n > 0) {
			return (int) Math.floor(div);
		}
		// n < 0, (div m n) = ceil(m/n)
		return (int) Math.ceil(div);
	}
}
