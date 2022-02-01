/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Factory for different types of variables.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <E>
 *            element type
 */
public class VariableFactory<E> {
	/**
	 * Types of variables for both the bisimulation and the simulation encoding.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum VariableType {
		/**
		 * Variable for which we want the number of true assignments maximized.
		 */
		MERGE,
		/**
		 * Ordinary (bi)simulation.
		 */
		ORDINARY,
		/**
		 * Direct (bi)simulation.
		 */
		DIRECT,
		/**
		 * Delayed (bi)simulation auxiliary variable indicating that duplicator satisfies the obligation.
		 */
		DELAYED_DUPLICATOR_ANSWERS,
		/**
		 * Delayed (bi)simulation auxiliary variable indicating that spoiler has a winning strategy.
		 */
		DELAYED_SPOILER_WINS
	}

	/**
	 * @param elem1
	 *            first element.
	 * @param elem2
	 *            second element
	 * @param type
	 *            variable type
	 * @return {@link Doubleton} of the respective type
	 */
	public Doubleton<E> getDoubleton(final E elem1, final E elem2, final VariableType type) {
		switch (type) {
			case MERGE:
				return new MergeDoubleton(elem1, elem2);
			case ORDINARY:
				return new OrdinaryDoubleton(elem1, elem2);
			case DIRECT:
				return new DirectDoubleton(elem1, elem2);
			case DELAYED_DUPLICATOR_ANSWERS:
				return new DelayedDuplicatorAnswersDoubleton(elem1, elem2);
			case DELAYED_SPOILER_WINS:
				return new DelayedSpoilerWinsDoubleton(elem1, elem2);
			default:
				throw new IllegalArgumentException("Unknown variable type " + type);
		}
	}

	/**
	 * @param elem1
	 *            first element.
	 * @param elem2
	 *            second element
	 * @param type
	 *            variable type
	 * @return {@link Pair} of the respective type
	 */
	public Pair<E, E> getPair(final E elem1, final E elem2, final VariableType type) {
		switch (type) {
			case MERGE:
				return new MergePair(elem1, elem2);
			case ORDINARY:
				return new OrdinaryPair(elem1, elem2);
			case DIRECT:
				return new DirectPair(elem1, elem2);
			case DELAYED_DUPLICATOR_ANSWERS:
				return new DelayedDuplicatorAnswersPair(elem1, elem2);
			case DELAYED_SPOILER_WINS:
				return new DelayedSpoilerWinsPair(elem1, elem2);
			default:
				throw new IllegalArgumentException("Unknown variable type " + type);
		}
	}

	/**
	 * {@link Doubleton} for expressing variables for which we want the number of true assignments maximized.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class MergeDoubleton extends Doubleton<E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public MergeDoubleton(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Doubleton} for expressing variables in the ordinary bisimulation encoding.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class OrdinaryDoubleton extends Doubleton<E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public OrdinaryDoubleton(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Doubleton} for expressing variables in the direct bisimulation encoding.
	 * <p>
	 * This variable exists for efficiency reasons because in the direct bisimulation encoding we can combine the
	 * variable for merging and for ordinary bisimulation into a single variable.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class DirectDoubleton extends Doubleton<E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public DirectDoubleton(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Doubleton} for expressing variables where duplicator satisfies her obligation in the delayed bisimulation
	 * encoding.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class DelayedDuplicatorAnswersDoubleton extends Doubleton<E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public DelayedDuplicatorAnswersDoubleton(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Doubleton} for expressing variables where spoiler wins in the delayed bisimulation encoding.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class DelayedSpoilerWinsDoubleton extends Doubleton<E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public DelayedSpoilerWinsDoubleton(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Pair} for expressing variables for which we want the number of true assignments maximized.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class MergePair extends Pair<E, E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public MergePair(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Pair} for expressing variables in the ordinary simulation encoding.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class OrdinaryPair extends Pair<E, E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public OrdinaryPair(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Pair} for expressing variables in the direct simulation encoding.
	 * <p>
	 * This variable exists for efficiency reasons because in the direct simulation encoding we can combine the variable
	 * for merging and for ordinary simulation into a single variable.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class DirectPair extends Pair<E, E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public DirectPair(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Pair} for expressing variables where duplicator satisfies her obligation in the delayed simulation
	 * encoding.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class DelayedDuplicatorAnswersPair extends Pair<E, E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public DelayedDuplicatorAnswersPair(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}

	/**
	 * {@link Pair} for expressing variables where spoiler wins in the delayed simulation encoding.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public class DelayedSpoilerWinsPair extends Pair<E, E> {
		/**
		 * @param elem1
		 *            first element.
		 * @param elem2
		 *            second element
		 */
		public DelayedSpoilerWinsPair(final E elem1, final E elem2) {
			super(elem1, elem2);
		}
	}
}
