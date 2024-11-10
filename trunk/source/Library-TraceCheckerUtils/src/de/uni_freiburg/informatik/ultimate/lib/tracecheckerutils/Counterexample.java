/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils;

import java.util.Collections;
import java.util.List;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Represents a counterexample trace (a word) with additional meta-information that might be relevant for trace checks.
 *
 * In particular, the class currently stores an <em>optional</em> list of control configurations visited in the program.
 * These may be {@link IcfgLocation}s (for sequential programs), arrays of {@link IcfgLocation}s indicating the current
 * location of different threads (for concurrent programs), or other and more complex objects. Users of this class
 * should not assume that the control locations implement anything beyond the methods of {@link Object}. Specifically,
 * we are only interested in when two configurations along the sequence are equal (in the sense of
 * {@link Object#equals(Object)}, as this indicates a loop (or recursion) in the program.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 */
public class Counterexample<L> {
	public static final String MISSING_CONTROL_CONFIGURATION_MESSAGE =
			"Counterexample with control configurations is required, "
					+ "but this counterexample does not have control configurations.";

	private final NestedWord<L> mWord;
	private final List<Object> mControlConfigurations;

	/**
	 * Creates a new instance that does not have any control configurations
	 *
	 * @param word
	 *            The word of the counterexample
	 */
	public Counterexample(final Word<L> word) {
		mWord = NestedWord.nestedWord(word);
		mControlConfigurations = null;
	}

	/**
	 * Creates a new counterexample with a list of control configurations.
	 *
	 * @param word
	 *            The word of the counterexample
	 * @param controlConfigurations
	 *            The list of control configurations visited along a trace
	 *
	 * @throws IllegalArgumentException
	 *             if the length of the control configurations does not match the word
	 */
	public Counterexample(final Word<L> word, final List<?> controlConfigurations) {
		mWord = NestedWord.nestedWord(Objects.requireNonNull(word));
		mControlConfigurations = List.copyOf(Objects.requireNonNull(controlConfigurations));

		if (controlConfigurations.size() != mWord.length() + 1) {
			throw new IllegalArgumentException("Number of control configurations does not match word length");
		}
	}

	public NestedWord<L> getWord() {
		return mWord;
	}

	/**
	 * @return the length of the trace of this counterexample.
	 */
	public int length() {
		return mWord.length();
	}

	public boolean hasControlConfigurations() {
		return mControlConfigurations != null;
	}

	/**
	 * Determines whether this counterexample contains control configurations, and if not, throws an
	 * {@link IllegalStateException} with the message {@value #MISSING_CONTROL_CONFIGURATION_MESSAGE}.
	 *
	 * @throws IllegalStateException
	 *             if the instance does not have control configurations
	 */
	public void requireControlConfigurations() {
		if (mControlConfigurations == null) {
			throw new IllegalStateException(MISSING_CONTROL_CONFIGURATION_MESSAGE);
		}
	}

	/**
	 * Retrieves the control configurations, if available. If this instance does not have control configurations,
	 * behaves as {@link #requireControlConfigurations()}.
	 *
	 * @throws IllegalStateException
	 *             if the instance does not have control configurations
	 */
	public List<Object> getControlConfigurations() {
		requireControlConfigurations();
		return Collections.unmodifiableList(mControlConfigurations);
	}
}
