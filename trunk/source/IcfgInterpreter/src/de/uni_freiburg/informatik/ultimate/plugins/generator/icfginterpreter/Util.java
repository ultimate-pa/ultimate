package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ReturnType;

public class Util {
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

	@SafeVarargs
	public static <T> HashSet<T> toHashSet(final T... terms) {
		return new HashSet<>(Arrays.asList(terms));
	}

	public static <T> T[] fillArray(final List<T> elements, final T[] newList) {
		for (int i = 0; i < newList.length && i < elements.size(); i++) {
			newList[i] = elements.get(i);
		}
		return newList;
	}

	/**
	 * Maps each object from some collection to a different object and stores it in the provided collection.
	 *
	 * @param <T>
	 *            The type of object that is stored in the given input collection
	 * @param <R>
	 *            The type of object that is stored in the given output collection
	 * @param <S>
	 *            The type of the output collection
	 * @param elements
	 *            A {@link Collection}<strong>&lt;T&gt;</strong>
	 * @param mapping
	 *            A function that takes an element of type <strong>&lt;T&gt;</strong> and returns an element of type
	 *            <strong>&lt;R&gt;</strong>
	 * @param out
	 *            A {@link Collection}<strong>&lt;R&gt;</strong>. Previous contents are removed.
	 * @return The same {@link Collection}<strong>&lt;R&gt;</strong> that was given as the <strong>out</strong>
	 *         parameter
	 */
	public static <T, R, S extends Collection<R>> S map(final Collection<T> elements, final Function<T, R> mapping,
			final S out) {
		final Iterator<T> iter = elements.iterator();
		out.clear();

		while (iter.hasNext()) {
			out.add(mapping.apply(iter.next()));
		}

		return out;
	}

	/**
	 * Maps each object from some collection to a pair of objects and stores them in the provided map.
	 *
	 * @param <T>
	 *            The type of object that is stored in the given input collection
	 * @param <R>
	 *            The type of object that is used as a key in the output map
	 * @param <S>
	 *            The type of object that is used as a value in the output map
	 * @param <U>
	 *            The type of map that will be returned
	 * @param elements
	 *            A {@link Collection} of elements of type <strong>&lt;T&gt;</strong>
	 * @param mapping
	 *            A function that takes an element of type <strong>&lt;T&gt;</strong> and returns an
	 *            {@link Entry}<strong>&lt;R,S&gt;</strong>
	 * @param out
	 *            A {@link Map}<strong>&lt;R,S&gt;</strong> that the mappings are stored in. Previous contents are
	 *            removed.
	 * @return The same {@link Map}<strong>&lt;R,S&gt;</strong> that was given as the <strong>out</strong> parameter
	 */
	public static <T, R, S, U extends Map<R, S>> U map(final Collection<T> elements,
			final Function<T, Entry<R, S>> mapping, final U out) {
		final Iterator<T> iter = elements.iterator();
		out.clear();

		while (iter.hasNext()) {
			final Entry<R, S> element = mapping.apply(iter.next());
			out.put(element.getKey(), element.getValue());
		}

		return out;
	}

	/**
	 * Maps each object from some array to a pair of objects and stores them in the provided map.
	 *
	 * @param <T>
	 *            The type of object that is stored in the given input array
	 * @param <R>
	 *            The type of object that is used as a key in the output map
	 * @param <S>
	 *            The type of object that is used as a value in the output map
	 * @param <U>
	 *            The type of map that will be returned
	 * @param elements
	 *            A {@link Collection} of elements of type <strong>&lt;T&gt;</strong>
	 * @param mapping
	 *            A function that takes an element of type <strong>&lt;T&gt;</strong> and returns an
	 *            {@link Entry}<strong>&lt;R,S&gt;</strong>
	 * @param out
	 *            A {@link Map}<strong>&lt;R,S&gt;</strong> that the mappings are stored in. Previous contents are
	 *            removed.
	 * @return The same {@link Map}<strong>&lt;R,S&gt;</strong> that was given as the <strong>out</strong> parameter
	 */
	public static <T, R, S, U extends Map<R, S>> U map(final T[] elements, final Function<T, Entry<R, S>> mapping,
			final U out) {
		out.clear();

		for (final T element : elements) {
			final Entry<R, S> entry = mapping.apply(element);
			out.put(entry.getKey(), entry.getValue());
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

	public static <T> ArrayList<T> filter(final T[] elements, final Predicate<T> isIncluded) {
		final ArrayList<T> out = new ArrayList<>();

		for (final T element : elements) {
			if (!isIncluded.test(element)) {
				continue;
			}
			out.add(element);
		}

		return out;
	}

	public static <T> boolean any(final Collection<T> elements, final Predicate<T> condition) {
		for (final T element : elements) {
			if (condition.test(element)) {
				return true;
			}
		}
		return false;
	}

	private final static HashMap<Sort[], Sort> arraySorts = new HashMap<>();

	public static FunctionSymbol makeFunction(final String symbol, final Theory theory, final Term... params) {
		final Sort[] sorts = new Sort[params.length];
		for (int i = 0; i < params.length; i++) {
			final Sort specificSort = params[i].getSort().getRealSort();
			sorts[i] = getGenericSort(specificSort, theory);
		}

		return theory.getFunctionWithResult(symbol, null, null, sorts);
	}

	public static Term makeConstant(final Object value, final ReturnType type, final Theory theory) {
		return makeConstant(value, getSort(type, theory), theory);
	}

	public static Term makeConstant(final Object value, final Sort type, final Theory theory) {
		return theory.constant(value, getGenericSort(type, theory));
	}

	public static TermVariable makeVariable(final String name, final Sort sort, final Theory theory) {
		return theory.createTermVariable(name, getGenericSort(sort, theory));
	}

	public static Term makeTerm(final String symbol, final Theory theory, final Term... params) {
		final FunctionSymbol function = makeFunction(symbol, theory, params);
		return theory.term(function, params);
	}

	public static Sort getSort(final ReturnType type, final Theory theory) {
		return getSort(type, theory, new Sort[0]);
	}

	public static String sortToCode(final Sort sort) {
		final StringBuilder out = new StringBuilder();

		return out.toString();
	}

	public static Sort getSort(final ReturnType type, final Theory theory, final Sort... args) {
		switch (type) {
		case Boolean:
			return theory.getBooleanSort();
		case Int:
			return theory.getNumericSort();
		case Array:
			assert args.length == 2;
			final Sort[] argsGeneric = { getGenericSort(args[0], theory), getGenericSort(args[1], theory) };

			Sort arraySort = arraySorts.getOrDefault(argsGeneric, null);
			if (arraySort == null) {
				arraySort = theory.getSort(SMTLIBConstants.ARRAY, argsGeneric);
				arraySorts.put(argsGeneric, arraySort);
			}
			return arraySort;
		case BitVector:
			assert args.length == 1 && args[0].isBitVecSort();
			return getGenericSort(args[0], theory);
		}
		return null;
	}

	private static Sort getGenericSort(final Sort sort, final Theory theory) {
		switch (sort.getName()) {
		case SMTLIBConstants.INT:
			return theory.getNumericSort();
		case SMTLIBConstants.BOOL:
			return theory.getBooleanSort();
		case SMTLIBConstants.BITVEC:

			final int length = Integer.parseInt(sort.getIndices()[0]);
			final String[] indices = { length + "" }; // TODO find out about sort indices representation
			return theory.getSort(SMTLIBConstants.BITVEC, indices);

		case SMTLIBConstants.ARRAY:
			final Sort[] args = new Sort[2];
			args[0] = getGenericSort(sort.getArguments()[0], theory);
			args[1] = getGenericSort(sort.getArguments()[1], theory);
			Sort arraySort = arraySorts.getOrDefault(args, null);
			if (arraySort == null) {
				arraySort = theory.getSort(SMTLIBConstants.ARRAY, args);
				arraySorts.put(args, arraySort);
			}
			return arraySort;
		}
		return null;
	}

	public static ReturnType getType(final Sort sort) {
		switch (sort.getName()) {
		case SMTLIBConstants.ARRAY:
			return ReturnType.Array;
		case SMTLIBConstants.BITVEC:
			return ReturnType.BitVector;
		case SMTLIBConstants.BOOL:
			return ReturnType.Boolean;
		case SMTLIBConstants.INT:
			return ReturnType.Int;
		}
		return null;
	}

	public static int compareBaseOrder(final ExecutionTerm a, final ExecutionTerm b) {
		return Integer.compare(a.hashCode(), b.hashCode());
	}

	public static String getIndent(final int depth) {
		return "\t".repeat(depth);
	}

	public static Long SMTDiv(final long m, final long n) {
		final Rational div = Rational.valueOf(m, n);
		if (n > 0) {
			// n > 0, (div m n) = floor(m/n)
			final Rational floorExact = div.floor();
			return floorExact.numerator().longValue() / floorExact.denominator().longValue();
		}
		// n < 0, (div m n) = ceil(m/n)
		final Rational ceilExact = div.ceil();
		return ceilExact.numerator().longValue() / ceilExact.denominator().longValue();
	}

	public static Long SMTMod(final Long m, final Long n) {
		// i == ((i / j) * j) + (i % j)
		// i % j == i - ((i / j) * j)
		final Rational div = Rational.valueOf(Util.SMTDiv(m, n), 1L);
		final Rational mSafe = Rational.valueOf(m, 1L);
		final Rational nSafe = Rational.valueOf(n, 1L);
		final Rational result = mSafe.sub(div.mul(nSafe));
		return result.numerator().longValueExact(); // should be long because all used numbers are long
	}

	public static long addSafe(final long x, final long y) {
		// adapted from Math.addExact(long, long)
		final long r = x + y;
		// HD 2-12 Overflow iff both arguments have the opposite sign of the result
		if (((x ^ r) & (y ^ r)) < 0) {
			return x < 0 ? Long.MIN_VALUE : Long.MAX_VALUE;
		}
		return r;
	}

	public static long subtractSafe(final long x, final long y) {
		// adapted from Math.subtractExact(long, long)
		final long r = x - y;
		// HD 2-12 Overflow iff the arguments have different signs and
		// the sign of the result is different from the sign of x
		if (((x ^ y) & (x ^ r)) < 0) {
			return x < 0 ? Long.MIN_VALUE : Long.MAX_VALUE;
		}
		return r;
	}

	public static String intToLetters(int numb) {
		final StringBuilder result = new StringBuilder();
		while (numb >= 0) {
			result.insert(0, (char) ('A' + (numb % 26)));
			numb = (numb / 26) - 1;
		}
		return result.toString();
	}

	public static int getBitVecLength(final Sort sort) {
		if (!sort.isBitVecSort()) {
			return -1;
		}
		return Integer.parseInt(sort.getIndices()[0]);
	}
}
