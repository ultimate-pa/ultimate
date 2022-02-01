/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.model.translation;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * Program Execution defined by a finite trace and (partial) program states at each position of this trace. This
 * interface is used to transport traces from an analyzer tool through the toolchain back to the user.
 *
 * @author heizmann@informatik.uni-freiburg.de
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <TE>
 *            Type of the elements whose sequence are the trace.
 * @param <E>
 *            Type of the expressions that are used to denote program variables and their values.
 */
public interface IProgramExecution<TE, E> extends Iterable<AtomicTraceElement<TE>> {

	/**
	 * Returns the length of this program execution. The length of a program execution is the length of the sequence of
	 * trace elements.
	 */
	int getLength();

	/**
	 * Returns the trace element at position <code>index<code> of this program execution.
	 */
	AtomicTraceElement<TE> getTraceElement(int index);

	/**
	 * Returns the partial program state at position <code>index<code> of this program execution. The partial program
	 * state at position <code>index<code> is the partial state of the program directly <b>after</b> executing the trace
	 * element at position <code>index<code>. Returns null if this object does not have any information about the
	 * program state at position <code>index<code>.
	 */
	ProgramState<E> getProgramState(int index);

	/**
	 * Returns the partial program state at the beginning of this program execution. This is the partial program state
	 * before the first trace element was executed.
	 */
	ProgramState<E> getInitialProgramState();

	/**
	 * @return The instance of {@link Class} describing the type of the type parameter E.
	 */
	Class<E> getExpressionClass();

	/**
	 * @return The instance of {@link Class} describing the type of the type parameter TE.
	 */
	Class<? extends TE> getTraceElementClass();

	/**
	 * Should return a human-readable representation of this program execution. Use {@link ProgramExecutionFormatter} to
	 * obtain it.
	 */
	@Override
	String toString();

	/**
	 * @return true if the program execution is for a concurrent program, false otherwise.
	 */
	boolean isConcurrent();

	/**
	 * @return A {@link List} of {@link ProgramState}s saved in this {@link IProgramExecution}. The list is always of
	 *         length {@link #getLength()} + 1 and may contain null elements (if the {@link IProgramExecution} does not
	 *         provide a program state for index <code>i</code>, the list at <code>i+1</code> is null).
	 */
	default List<ProgramState<E>> getProgramStates() {
		final List<ProgramState<E>> rtr = new ArrayList<>(getLength() + 1);
		rtr.add(getInitialProgramState());
		for (int i = 0; i < getLength(); ++i) {
			rtr.add(getProgramState(i));
		}
		return rtr;
	}

	@Override
	default Spliterator<AtomicTraceElement<TE>> spliterator() {
		return Spliterators.spliterator(iterator(), getLength(),
				Spliterator.SIZED | Spliterator.IMMUTABLE | Spliterator.ORDERED);
	}

	/**
	 * Returns a sequential {@code Stream} with this collection as its source.
	 *
	 * @return a sequential {@code Stream} over the atomic trace elements of this program execution
	 */
	default Stream<AtomicTraceElement<TE>> stream() {
		return StreamSupport.stream(spliterator(), false);
	}

	@Override
	default Iterator<AtomicTraceElement<TE>> iterator() {
		return new Iterator<AtomicTraceElement<TE>>() {

			private final int max = getLength();
			private int current = 0;

			@Override
			public boolean hasNext() {
				return current < max;
			}

			@Override
			public AtomicTraceElement<TE> next() {
				return getTraceElement(current++);
			}
		};
	}

	/**
	 * @return an {@link IBacktranslationValueProvider} for this type.
	 */
	IBacktranslationValueProvider<TE, E> getBacktranslationValueProvider();

	/**
	 * @param <E>
	 *            Type of the expressions that are used to denote program variables and their values.
	 * @param <TE>
	 *            Type of the elements whose sequence are the trace.
	 */
	public static <TE, E> IProgramExecution<TE, E> emptyExecution(final Class<E> exprClass,
			final Class<? extends TE> teClass) {
		return new IProgramExecution<TE, E>() {

			@Override
			public int getLength() {
				return 0;
			}

			@Override
			public AtomicTraceElement<TE> getTraceElement(final int index) {
				return null;
			}

			@Override
			public ProgramState<E> getProgramState(final int index) {
				return null;
			}

			@Override
			public ProgramState<E> getInitialProgramState() {
				return null;
			}

			@Override
			public Class<E> getExpressionClass() {
				return exprClass;
			}

			@Override
			public Class<? extends TE> getTraceElementClass() {
				return teClass;
			}

			@Override
			public IBacktranslationValueProvider<TE, E> getBacktranslationValueProvider() {
				return null;
			}

			@Override
			public boolean isConcurrent() {
				return false;
			}
		};
	}

	/**
	 * Program state that is can be defined only partially. This class defines for some variables of the program a
	 * Collection of possible values. Variables and values are expressions of type E. We use a map to assign to each
	 * variable a set of possible values.
	 *
	 * @author heizmann@informatik.uni-freiburg.de
	 * @author dietsch@informatik.uni-freiburg.de
	 */
	public class ProgramState<E> {
		private final Class<E> mClassOfExpression;
		private final Map<E, Collection<E>> mVariable2Values;

		public ProgramState(final Map<E, Collection<E>> variable2Values, final Class<E> classOfExpression) {
			super();
			mClassOfExpression = classOfExpression;
			mVariable2Values = variable2Values;
		}

		public Set<E> getVariables() {
			return mVariable2Values.keySet();
		}

		public Collection<E> getValues(final E variable) {
			return mVariable2Values.get(variable);
		}

		public Class<E> getClassOfExpression() {
			return mClassOfExpression;
		}

		/**
		 * @param expressionToString
		 *            Function that maps each expression of type E to a string.
		 */
		public String toString(final Function<E, String> expressionToString) {
			final List<Entry<E, Collection<E>>> toSort = constructSortedListOfEntries(mVariable2Values);
			final StringBuilder sb = new StringBuilder();
			boolean first = true;
			for (final Entry<E, Collection<E>> entry : toSort) {
				if (first) {
					first = false;
				} else {
					sb.append(", ");
				}
				sb.append(expressionToString.apply(entry.getKey()));
				if (entry.getValue().size() == 1) {
					sb.append("=");
					final E theElement = entry.getValue().iterator().next();
					sb.append(expressionToString.apply(theElement));
				} else {
					// TODO 20190604 Matthias: replace by UTF-8 ∈ if this
					// does not lead to problems with web interface
					// or other use interfaces
					sb.append(" in");
					sb.append(entry.getValue().stream().map(expressionToString).collect(Collectors.joining(",")));
				}
			}
			return sb.toString();
		}

		private static <E> List<Entry<E, Collection<E>>>
				constructSortedListOfEntries(final Map<E, Collection<E>> variable2values) {
			final List<Entry<E, Collection<E>>> toSort = new ArrayList<>(variable2values.entrySet());
			Collections.sort(toSort, new Comparator<Entry<E, Collection<E>>>() {
				@Override
				public int compare(final Entry<E, Collection<E>> arg0, final Entry<E, Collection<E>> arg1) {
					return arg0.getKey().toString().compareToIgnoreCase(arg1.getKey().toString());
				}
			});
			return toSort;
		}

		@Override
		public String toString() {
			return toString(String::valueOf);
		}
	}
}
