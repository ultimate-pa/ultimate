/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automaton Delta Debugger.
 * 
 * The ULTIMATE Automaton Delta Debugger is free software: you can redistribute
 * it and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * The ULTIMATE Automaton Delta Debugger is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser
 * General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automaton Delta Debugger. If not, see
 * <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7: If you modify the
 * ULTIMATE Automaton Delta Debugger, or any covered work, by linking or
 * combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automaton Delta Debugger grant you additional
 * permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AbstractShrinker;

/**
 * Abstract debugging policy with common tasks.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            shrinker data structure
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class AbstractDebug<T, LETTER, STATE> {
	protected final AbstractTester<LETTER, STATE> mTester;
	protected final AbstractShrinker<T, LETTER, STATE> mShrinker;

	/**
	 * Policy for delta debugging a list of items.
	 */
	public enum DebugPolicy {
		/**
		 * Apply a single change at a time.
		 */
		SINGLE,
		/**
		 * Apply many changes at a time in binary search manner.
		 */
		BINARY
	}

	/**
	 * @param tester
	 *            Tester.
	 * @param shrinker
	 *            shrinker
	 */
	public AbstractDebug(final AbstractTester<LETTER, STATE> tester,
			final AbstractShrinker<T, LETTER, STATE> shrinker) {
		mTester = tester;
		mShrinker = shrinker;
	}

	/**
	 * Runs the search for the current shrinker.
	 * 
	 * @return true iff the sublist could be shrunk
	 */
	public abstract boolean run();

	@Override
	public String toString() {
		return getClass().getSimpleName();
	}

	/**
	 * Executes sublist test and informs the shrinker.
	 * 
	 * @param list
	 *            list of shrinking elements to be executed
	 * @return true iff shrinking was successful
	 */
	protected boolean test(final List<T> list) {
		// initialize test for the sublist
		final INestedWordAutomaton<LETTER, STATE> automaton = mShrinker.createAutomaton(list);

		// run test
		final boolean isTestSuccessful = mTester.test(automaton);

		if (isTestSuccessful) {
			// error reproduced
			mShrinker.error(automaton);
			errorAction();
		} else {
			// error not reproduced
			mShrinker.noError(automaton);
			noErrorAction();
		}
		return isTestSuccessful;
	}

	/**
	 * Executed when the shrinking was successful.
	 */
	protected abstract void errorAction();

	/**
	 * Executed when the shrinking was not successful.
	 */
	protected abstract void noErrorAction();
}
