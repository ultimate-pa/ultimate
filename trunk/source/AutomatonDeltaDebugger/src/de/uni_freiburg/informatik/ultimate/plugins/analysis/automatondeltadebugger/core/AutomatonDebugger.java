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

import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.core.AbstractDebug.DebugPolicy;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.factories.INestedWordAutomatonFactory;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.AbstractShrinker;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.shrinkers.BridgeShrinker;

/**
 * Delta debugger for automaton-related methods. This is the main class to run the delta debugger. To run it, the user
 * needs the following ingredients:
 * <ol>
 * <li>an initial {@link INestedWordAutomaton} object</li>
 * <li>a {@link INestedWordAutomatonFactory} which can create new automaton objects</li>
 * <li>a {@link AbstractTester} that executes the method under consideration on automaton objects and checks whether the
 * same type of error as in the original (unshrunk) problem still occurs.</li>
 * </ol>
 * At 2. It is advised that the factory returns objects of the same type as the initial automaton in 1. to exclude the
 * possibility that the bug comes from different sources. This is, however, not a constraint of the class. At 3. It is
 * possible to check for any type of {@link Throwable} as an error. However, in order to prevent misinterpretation by
 * more than one possible sources of the error, it is advised that the error is of a unique type. For instance, if the
 * method code under consideration is available, the {@link DebuggerException} could be thrown at the place where the
 * designated error occurs. Example: If the user wants to find the cause for an {@link AutomataLibraryException}, this
 * might be introduced during the process of shrinking the automaton as well.<br>
 * For further explanations see {@link #shrink(List, List)}.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class AutomatonDebugger<LETTER, STATE> {
	private static final int STRING_BUFFER_MIN_SIZE = 71;

	private final IUltimateServiceProvider mServices;
	private INestedWordAutomaton<LETTER, STATE> mAutomaton;
	private final INestedWordAutomatonFactory<LETTER, STATE> mFactory;
	private final AbstractTester<LETTER, STATE> mTester;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param automaton
	 *            automaton
	 * @param factory
	 *            automaton factory
	 * @param tester
	 *            tester
	 */
	public AutomatonDebugger(final IUltimateServiceProvider services,
			final INestedWordAutomaton<LETTER, STATE> automaton,
			final INestedWordAutomatonFactory<LETTER, STATE> factory, final AbstractTester<LETTER, STATE> tester) {
		mServices = services;
		mAutomaton = automaton;
		mFactory = factory;
		mTester = tester;
	}

	/**
	 * Shrinks an automaton according to given rules.
	 * <p>
	 * Given a set of rules to shrink the automaton, we apply the rules to shrink the respective automaton objects
	 * (e.g., states). As long as one shrinking process was successful, we repeat this procedure.
	 * <p>
	 * Next we apply {@link BridgeShrinker}s which require a more complicated control logic. This opens another loop
	 * inside which all the shrinkers from above.
	 * <p>
	 * Finally, we apply a second set of shrinking rules which make sense only once (e.g., shrinking the alphabet).
	 * 
	 * @param shrinkersLoop
	 *            list of shrinkers (shrinking rules) applied in loop
	 * @param shrinkersBridge
	 *            list of shrinkers (shrinking rules) applied after each loop
	 * @param shrinkersEnd
	 *            list of shrinkers (shrinking rules) applied once
	 * @param policy
	 *            debug policy
	 * @return shrunk automaton
	 * @see AbstractDebug
	 */
	public INestedWordAutomaton<LETTER, STATE> shrink(final List<AbstractShrinker<?, LETTER, STATE>> shrinkersLoop,
			final List<BridgeShrinker<?, LETTER, STATE>> shrinkersBridge,
			final List<AbstractShrinker<?, LETTER, STATE>> shrinkersEnd, final DebugPolicy policy) {
		// apply loop shrinkers until nothing has changed
		applyLoopShrinkers(shrinkersLoop, policy);

		// now try the bridge shrinkers
		applyBridgeShrinkers(shrinkersLoop, shrinkersBridge, policy);

		// in the end, try the final shrinkers (applied only once)
		applyShrinkers(shrinkersEnd, policy);

		return mAutomaton;
	}

	private boolean applyLoopShrinkers(final List<AbstractShrinker<?, LETTER, STATE>> shrinkersLoop,
			final DebugPolicy policy) {
		boolean isReducedAtLeastOnce = false;
		boolean isReduced;
		do {
			isReduced = applyShrinkers(shrinkersLoop, policy);
			isReducedAtLeastOnce |= isReduced;
		} while (isReduced);
		return isReducedAtLeastOnce;
	}

	private void applyBridgeShrinkers(final List<AbstractShrinker<?, LETTER, STATE>> shrinkersLoop,
			final List<BridgeShrinker<?, LETTER, STATE>> shrinkersBridge, final DebugPolicy policy) {
		final List<BridgeShrinker<?, LETTER, STATE>> shrinkersBridgeCopy = new LinkedList<>(shrinkersBridge);
		final INestedWordAutomaton<LETTER, STATE> automatonBackup = mAutomaton;
		boolean isReducedAtLeastOnceByAny = false;
		while (!shrinkersBridgeCopy.isEmpty()) {
			final BridgeShrinker<?, LETTER, STATE> bridge = shrinkersBridgeCopy.get(0);
			final boolean bridgeReduced = applyShrinkers(Collections.singletonList(bridge), policy);
			if (!bridgeReduced) {
				// the bridge did not change anything, try the next one (the automaton did not change)
				shrinkersBridgeCopy.remove(0);
				break;
			}

			// now run all loop shrinkers again on the result
			final boolean isReducedAtLeastOnce = applyLoopShrinkers(shrinkersLoop, policy);

			if (isReducedAtLeastOnce) {
				// the bridge triggered a change, so it might be useful in the future; enqueue to bridges again
				bridge.reset(mAutomaton);
				shrinkersBridgeCopy.remove(0);
				shrinkersBridgeCopy.add(bridge);
				isReducedAtLeastOnceByAny = true;
			} else if (bridge.isFinished()) {
				// the bridge did nothing and is finished, remove it (only a short-hand, would happen anyway)
				shrinkersBridgeCopy.remove(0);
			}
		}
		if (!isReducedAtLeastOnceByAny) {
			// reset the factory (most bridge shrinkers edit it, here we reset it once)
			mFactory.setAutomaton(automatonBackup);

			// not necessary, but the rationale is that we should not change the input too much if it does not help
			mAutomaton = automatonBackup;
		}
	}

	/**
	 * Runs a binary search for each shrinker in a list.
	 * 
	 * @param shrinkers
	 *            list of shrinkers (shrinking rules)
	 * @param policy
	 *            debug policy
	 * @return true iff at least one shrinker was successful
	 * @see AbstractDebug
	 */
	private boolean applyShrinkers(final List<AbstractShrinker<?, LETTER, STATE>> shrinkers, final DebugPolicy policy) {
		boolean isReduced = false;
		for (final AbstractShrinker<?, LETTER, STATE> shrinker : shrinkers) {
			if (isTimeoutRequested()) {
				break;
			}

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
		final StringBuilder builder = new StringBuilder(STRING_BUFFER_MIN_SIZE);
		// @formatter:off
		builder.append("<debugger with ")
				.append(mFactory)
				.append(" and ")
				.append(mTester)
				.append(", currently considering the following automaton:\n")
				.append(mAutomaton)
				.append('>');
		// @formatter:on
		return builder.toString();
	}

	private boolean isTimeoutRequested() {
		return !mServices.getProgressMonitorService().continueProcessing();
	}
}
