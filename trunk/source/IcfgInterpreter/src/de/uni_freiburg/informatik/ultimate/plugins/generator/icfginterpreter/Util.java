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
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.ArrayDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.BooleanDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.Domain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.IntegerDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;

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

	public static <T> T[] fillArray(final List<T> elements, final T[] newList) {
		for (int i = 0; i < newList.length && i < elements.size(); i++) {
			newList[i] = elements.get(i);
		}
		return newList;
	}

	/**
	 * Maps each object from some collection to a different object and stores it in the provided collection.
	 *
	 * @param <T>      The type of object that is stored in the given input collection
	 * @param <R>      The type of object that is stored in the given output collection
	 * @param <S>      The type of the output collection
	 * @param elements A {@link Collection}<strong>&lt;T&gt;</strong>
	 * @param mapping  A function that takes an element of type <strong>&lt;T&gt;</strong> and returns an element of
	 *                 type <strong>&lt;R&gt;</strong>
	 * @param out      A {@link Collection}<strong>&lt;R&gt;</strong>. Previous contents are removed.
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
	 * @param <T>      The type of object that is stored in the given input collection
	 * @param <R>      The type of object that is used as a key in the output map
	 * @param <S>      The type of object that is used as a value in the output map
	 * @param <U>      The type of map that will be returned
	 * @param elements A {@link Collection} of elements of type <strong>&lt;T&gt;</strong>
	 * @param mapping  A function that takes an element of type <strong>&lt;T&gt;</strong> and returns an
	 *                 {@link Entry}<strong>&lt;R,S&gt;</strong>
	 * @param out      A {@link Map}<strong>&lt;R,S&gt;</strong> that the mappings are stored in. Previous contents are
	 *                 removed.
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
	 * @param <T>      The type of object that is stored in the given input array
	 * @param <R>      The type of object that is used as a key in the output map
	 * @param <S>      The type of object that is used as a value in the output map
	 * @param <U>      The type of map that will be returned
	 * @param elements A {@link Collection} of elements of type <strong>&lt;T&gt;</strong>
	 * @param mapping  A function that takes an element of type <strong>&lt;T&gt;</strong> and returns an
	 *                 {@link Entry}<strong>&lt;R,S&gt;</strong>
	 * @param out      A {@link Map}<strong>&lt;R,S&gt;</strong> that the mappings are stored in. Previous contents are
	 *                 removed.
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

	public static <T> boolean any(final Collection<T> elements, final Predicate<T> condition) {
		for (final T element : elements) {
			if (condition.test(element)) {
				return true;
			}
		}
		return false;
	}

	/* Quantifier-free Arrays, Bit-Vectors, and integer maths */
	// private static Theory mTheory;// = new Theory(Logics.AUFBVDTNIA);// QF_AUFBVLIA);
	// private final static Sort booleanSort = theory.getBooleanSort();
	// private final static Sort integerSort = theory.getNumericSort();
	/**
	 * The generic array sorts by
	 */
	private final static HashMap<Sort[], Sort> arraySorts = new HashMap<>();

	/*
	 * public static Theory getTheory() { return theory; }
	 */

	public static FunctionSymbol makeFunction(final String symbol, final Theory theory, final Term... params) {
		final Sort[] sorts = new Sort[params.length];
		for (int i = 0; i < params.length; i++) {
			final Sort specificSort = params[i].getSort().getRealSort();
			// sorts must be same instance for functionSymbol
			sorts[i] = getGenericSort(specificSort, theory);
		}
		// sorts[params.length] = resultSort;

		return theory.getFunctionWithResult(symbol, null, null, sorts);
	}

	public static Term makeConstant(final Object value, final ReturnType type, final Theory theory) {
		return makeConstant(value, getSort(type, theory), theory);
	}

	public static Term makeConstant(final Object value, final Sort type, final Theory theory) {
		return theory.constant(value, getGenericSort(type, theory));
	}

	public static TermVariable makeVariable(final TermVariable term, final Theory theory) {
		return makeVariable(term.getName(), term.getSort(), theory);
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

	public static Sort getSort(final ReturnType type, final Theory theory, final Sort... args) {
		switch (type) {
		case Boolean:
			return theory.getBooleanSort();// booleanSort;
		case Int:
			return theory.getNumericSort();// integerSort;
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
			// use appropriate method
			break;
		}
		return null;
	}

	private static Sort getGenericSort(final Sort sort, final Theory theory) {
		switch (sort.getName()) {
		case SMTLIBConstants.INT:
			return theory.getNumericSort();// integerSort;
		case SMTLIBConstants.BOOL:
			return theory.getBooleanSort();// booleanSort;
		case SMTLIBConstants.BITVEC:
			break; // TODO
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

	@SuppressWarnings("unchecked")
	public static <T extends Domain<T>> T constructFullDomain(final Sort sort) {
		switch (sort.getName()) {
		case SMTLIBConstants.ARRAY:
			final Sort[] keyValue = sort.getArguments();
			return (T) getArrayDomain(keyValue[0], keyValue[1]);
		case SMTLIBConstants.BITVEC:
			break; // TODO
		case SMTLIBConstants.BOOL:
			return (T) new BooleanDomain().getFullDomain();
		case SMTLIBConstants.INT:
			return (T) new IntegerDomain().getFullDomain();
		}

		return null;
	}

	private static <keyType extends Domain<keyType>, valueType extends Domain<valueType>> ArrayDomain<keyType, valueType> getArrayDomain(
			final Sort keySort, final Sort valueSort) {

		return new ArrayDomain<keyType, valueType>(new HashMap<>(), constructFullDomain(keySort),
				constructFullDomain(valueSort));
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
