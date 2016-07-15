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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.ADebug.EDebugPolicy;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.factories.AAutomatonFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AShrinker;

/**
 * Delta debugger for automaton-related methods.
 * 
 * This is the main class to run the delta debugger. To run it, the user needs
 * the following ingredients: 1) an initial {@link INestedWordAutomaton} object
 * 2) a {@link AAutomatonFactory} which can create new automaton objects 3) a
 * {@link ATester} which executes the method under consideration on automaton
 * objects and checks whether the same type of error as in the original
 * (unshrunk) problem still occurs.
 * 
 * At 2) It is advised that the factory returns objects of the same type as the
 * initial automaton in 1) to exclude the possibility that the bug comes from
 * different sources. This is, however, not a constraint of the class.
 * 
 * At 3) It is possible to check for any type of {@link Throwable} as an error.
 * However, in order to prevent misinterpretation by more than one possible
 * sources of the error, it is advised that the error is of a unique type. For
 * instance, if the method code under consideration is available, the
 * {@link DebuggerException} could be thrown at the place where the designated
 * error occurs. Example: If the user wants to find the cause for an
 * {@link AutomataLibraryException}, this might be introduced during the process
 * of shrinking the automaton as well.
 * 
 * For further explanations see {@link #shrink(List, List)}.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class AutomatonDebugger<LETTER, STATE> {
	private INestedWordAutomaton<LETTER, STATE> mAutomaton;
	private final AAutomatonFactory<LETTER, STATE> mFactory;
	private final ATester<LETTER, STATE> mTester;
	
	/**
	 * @param automaton automaton
	 * @param factory automaton factory
	 * @param tester tester
	 */
	public AutomatonDebugger(
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final AAutomatonFactory<LETTER, STATE> factory,
			final ATester<LETTER, STATE> tester) {
		this.mAutomaton = automaton;
		this.mFactory = factory;
		this.mTester = tester;
	}
	
	/**
	 * Shrinks an automaton according to given rules.
	 * 
	 * Given a set of rules to shrink the automaton, we apply binary search on
	 * the respective automaton objects (e.g., states). As long as one shrinking
	 * process was successful, we repeat this procedure. Finally, we apply a
	 * second set of shrinking rules which make sense only once (e.g., shrinking
	 * the alphabet).
	 * 
	 * @see BinaryDebug
	 * @param shrinkersLoop list of shrinkers (shrinking rules) applied in loop
	 * @param shrinkersEnd list of shrinkers (shrinking rules) applied once
	 * @param policy debug policy
	 * @return shrunk automaton
	 */
	public INestedWordAutomaton<LETTER, STATE> shrink(
			final List<AShrinker<?, LETTER, STATE>> shrinkersLoop,
			final List<AShrinker<?, LETTER, STATE>> shrinkersEnd,
			final EDebugPolicy policy) {
		// loop through shrinkers until nothing has changed
		boolean isReduced = true;
		while (isReduced) {
			isReduced = applyShrinkers(shrinkersLoop, policy);
		}
		// final shrinkers (apply only once)
		applyShrinkers(shrinkersEnd, policy);
		return mAutomaton;
	}
	
	/**
	 * Runs a binary search for each shrinker in a list.
	 * 
	 * @see BinaryDebug
	 * @param shrinkers list of shrinkers (shrinking rules)
	 * @param policy debug policy
	 * @return true iff at least one shrinker was successful
	 */
	private boolean
			applyShrinkers(final List<AShrinker<?, LETTER, STATE>> shrinkers,
					final EDebugPolicy policy) {
		boolean isReduced = false;
		for (final AShrinker<?, LETTER, STATE> shrinker : shrinkers) {
			final INestedWordAutomaton<LETTER, STATE> newAutomaton =
					shrinker.runSearch(mAutomaton, mTester, mFactory, policy);
			if (newAutomaton != null) {
				// store shrunk automaton
				mAutomaton = newAutomaton;
				isReduced = true;
			}
		}
		return isReduced;
	}
	
	@Override
	public String toString() {
		final StringBuilder b = new StringBuilder();
		b.append("<debugger with ");
		b.append(mFactory);
		b.append(" and ");
		b.append(mTester);
		b.append(", currently considering the following automaton:\n");
		b.append(mAutomaton);
		b.append(">");
		return b.toString();
	}
}
