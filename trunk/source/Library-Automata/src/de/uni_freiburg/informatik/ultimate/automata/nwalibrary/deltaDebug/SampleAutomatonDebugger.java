/*
 * Copyright (C) 2015 Christian Schilling <schillic@informatik.uni-freiburg.de>
 * Copyright (C) 2009-2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.deltaDebug;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StringFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.services.ToolchainStorage;

/**
 * Exemplary usage of the {@link AutomatonDebugger}.
 * 
 * @author Christian Schilling <schillic@informatik.uni-freiburg.de>
 */
public class SampleAutomatonDebugger {
	public static void main(String[] args) {
		// service provider (needed for the automaton and automaton factory)
		final IUltimateServiceProvider services = new ToolchainStorage();
		
		// use automata of type "string"
		final StateFactory<String> stateFactory = new StringFactory();
		
		// automaton
		final INestedWordAutomaton<String, String> automaton =
				getSampleAutomaton(services, stateFactory);
		
		// automaton factory
		final AAutomatonFactory<String, String> automatonFactory =
				new NestedWordAutomatonFactory<String, String>(
						stateFactory, automaton, services);
		
		// tester
		final ATester<String, String> tester =
				new SampleTester<String, String>();
		
		// delta debugger
		final AutomatonDebugger<String, String> debugger =
				new AutomatonDebugger<String, String>(
						automaton, automatonFactory, tester);
		
		// list of shrinkers (i.e., rules to apply) to be applied iteratively
		final List<AShrinker<?, String, String>> shrinkersLoop =
				new ArrayList<AShrinker<?, String, String>>();
		shrinkersLoop.add(new StateShrinker<String, String>());
		
		// list of shrinkers (i.e., rules to apply) to be applied only once
		final List<AShrinker<?, String, String>> shrinkersEnd =
				new ArrayList<AShrinker<?, String, String>>();
		shrinkersEnd.add(new UnusedLetterShrinker<String, String>());
		
		// execute delta debugger (binary search)
		final INestedWordAutomaton<String, String> result =
				debugger.shrink(shrinkersLoop, shrinkersEnd);
		
		// print result
		System.out.println(
				"The automaton debugger terminated resulting in the following automaton:");
		System.out.println(result);
	}
	
	/**
	 * @param services service provider
	 * @param stateFactory state factory
	 * @return a sample automaton
	 */
	private static INestedWordAutomaton<String, String> getSampleAutomaton(
			final IUltimateServiceProvider services,
			final StateFactory<String> stateFactory) {
		final HashSet<String> internals = new HashSet<String>();
		internals.add("a");
		internals.add("b");
		internals.add("c");
		internals.add("d");
		final HashSet<String> calls = new HashSet<String>();
		final HashSet<String> returns = new HashSet<String>();
		
		NestedWordAutomaton<String, String> automaton =
				new NestedWordAutomaton<String, String>(services, internals,
						calls, returns, stateFactory);
		
		automaton.addState(true, false, "q0");
		automaton.addState(false, false, "q1");
		automaton.addState(false, false, "q2");
		automaton.addState(false, false, "q3");
		automaton.addState(false, false, "q4");
		automaton.addState(false, true, "q5");
		
		automaton.addInternalTransition("q0", "a", "q1");
		automaton.addInternalTransition("q1", "a", "q2");
		automaton.addInternalTransition("q2", "a", "q3");
		automaton.addInternalTransition("q3", "a", "q4");
		automaton.addInternalTransition("q4", "a", "q5");
		
		return automaton;
	}
	
	/**
	 * Sample tester which throws an error whenever the automaton contains
	 * a state "q1" or "q3".
	 */
	static class SampleTester<LETTER, STATE>
			extends ATester<LETTER, STATE> {
		public SampleTester() {
			super(new DebuggerException(null, "test exception"));
		}
		
		@Override
		public void execute(INestedWordAutomaton<LETTER, STATE> automaton)
				throws DebuggerException {
			boolean result = true;
			result &= ! automaton.getStates().contains("q1");
			result &= ! automaton.getStates().contains("q3");
			if (! result) {
				throw new DebuggerException(this.getClass(), "test exception");
			}
		}
	}
}