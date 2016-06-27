/*
 * Copyright (C) 2015-2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.ADebug;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.ADebug.EDebugPolicy;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.ATester;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.BinaryDebug;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.SingleDebug;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.factories.AAutomatonFactory;

/**
 * Shrinks an automaton according to a certain criterion while still producing
 * the same error.
 * 
 * A shrinker can be seen as a rule according to which the debugger tries to
 * shrink an automaton. For this purpose the shrinker defines a list of objects
 * which are to be removed and then applies binary search on this list.
 * 
 * Implementing subclasses should make certain that no exception is thrown
 * during construction of shrunk automata. Otherwise this might lead to unwanted
 * behavior, namely the debugger might return an automaton object which has
 * crashed during construction (e.g., a transition was inserted whose state or
 * letter was not present).
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 * @param <T> type of objects to be removed, e.g., states
 */
public abstract class AShrinker<T, LETTER, STATE> {
	protected INestedWordAutomaton<LETTER, STATE> mAutomaton;
	protected AAutomatonFactory<LETTER, STATE> mFactory;
	
	/**
	 * Creates an automaton.
	 * 
	 * NOTE: Implementing subclasses must store the automaton.
	 * 
	 * @param list list of objects to be removed
	 * @return automaton according to (complement of the) list
	 */
	public abstract INestedWordAutomaton<LETTER, STATE>
			createAutomaton(final List<T> list);
			
	/**
	 * Extracts a list of objects containing all respective objects of the
	 * current automaton.
	 * 
	 * @return list of objects to be removed
	 */
	public abstract List<T> extractList();
	
	/**
	 * Called when the error still occurs for a shrunk automaton (-> success).
	 * 
	 *  @param newAutomaton new automaton
	 */
	public void error(final INestedWordAutomaton<LETTER, STATE> newAutomaton) {
		// use shrunk automaton henceforth
		mAutomaton = newAutomaton;
	}
	
	/**
	 * Called when no error occurs for a shrunk automaton (-> failure).
	 * 
	 * @param newAutomaton new automaton
	 */
	public void
			noError(final INestedWordAutomaton<LETTER, STATE> newAutomaton) {
		// no action for standard shrinker
	}
	
	/**
	 * Runs a binary search according to the shrinking rule implemented by this
	 * shrinker.
	 * 
	 * @param automaton automaton
	 * @param tester tester
	 * @param factory automaton factory
	 * @param policy debug policy
	 * @return new automaton iff automaton could be shrunk
	 */
	public INestedWordAutomaton<LETTER, STATE> runSearch(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final ATester<LETTER, STATE> tester,
			final AAutomatonFactory<LETTER, STATE> factory,
			final EDebugPolicy policy) {
		mAutomaton = automaton;
		mFactory = factory;
		final ADebug<T, LETTER, STATE> debugger;
		switch (policy) {
			case SINGLE:
				debugger = new SingleDebug<T, LETTER, STATE>(tester, this);
				break;
			
			case BINARY:
				debugger = new BinaryDebug<T, LETTER, STATE>(tester, this);
				break;
			
			default:
				throw new IllegalArgumentException("Unknown policy.");
		}
		final boolean isReduced = debugger.run();
		return isReduced ? mAutomaton : null;
	}
	
	@Override
	public String toString() {
		return this.getClass().getSimpleName();
	}
}
