/*
 * Copyright (C) 2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;

/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class PathProgramAutomatonConstructor<LETTER extends IIcfgTransition<?>> {

	/**
	 * A mapping from positions of given path to states of the constructed automaton.
	 */
	private List<IPredicate> mPositionsToStates;

	public List<IPredicate> getPositionsToStates() {
		return mPositionsToStates;
	}

	/**
	 * Construct a path automaton (finite) from the given path.
	 */
	public INestedWordAutomaton<LETTER, IPredicate> constructAutomatonFromGivenPath(final NestedWord<LETTER> path,
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final PredicateFactory predicateFactory, final TAPreferences taPrefs) {
		// Set the alphabet
		final Set<LETTER> internalAlphabet = new HashSet<>();
		final Set<LETTER> callAlphabet = new HashSet<>();
		final Set<LETTER> returnAlphabet = new HashSet<>();
		for (int i = 0; i < path.length(); i++) {
			if (path.isInternalPosition(i)) {
				internalAlphabet.add(path.getSymbol(i));
			} else if (path.isCallPosition(i)) {
				callAlphabet.add(path.getSymbol(i));
			} else if (path.isReturnPosition(i)) {
				returnAlphabet.add(path.getSymbol(i));
			} else {
				throw new UnsupportedOperationException(
						"Symbol at position " + i + " is neither internal, call, nor return symbol!");
			}
		}

		final IEmptyStackStateFactory<IPredicate> predicateFactoryFia = new PredicateFactoryForInterpolantAutomata(
				csToolkit.getManagedScript(), predicateFactory, taPrefs.computeHoareAnnotation());
		// Create the automaton
		final NestedWordAutomaton<LETTER, IPredicate> pathPA = new NestedWordAutomaton<>(
				new AutomataLibraryServices(services),
				new VpAlphabet<>(internalAlphabet, callAlphabet, returnAlphabet), predicateFactoryFia);

		// We need this list to create the transitions of the automaton.
		mPositionsToStates = new ArrayList<>(path.length() + 1);

		final IcfgLocation[] arrOfProgPoints = new BoogieIcfgLocation[path.length()];
		// We use this map to keep track of the predicates we've created so far. We don't want to create a new predicate
		// for the same program point, therefore we use the map to get the predicate we've constructed before.
		final Map<IcfgLocation, SPredicate> programPointToState = new HashMap<>();

		IcfgLocation tempProgramPoint = path.getSymbol(0).getSource();
		// Add the initial state
		final Term trueTerm = csToolkit.getManagedScript().getScript().term("true");
		final SPredicate initialState = predicateFactory.newSPredicate(tempProgramPoint, trueTerm);
		pathPA.addState(true, false, initialState);
		programPointToState.put(tempProgramPoint, initialState);
		mPositionsToStates.add(0, initialState);

		// Add the other states
		for (int i = 0; i < path.length(); i++) {
			tempProgramPoint = path.getSymbol(i).getTarget();
			if (!programPointToState.containsKey(tempProgramPoint)) {
				final SPredicate newState = predicateFactory.newSPredicate(tempProgramPoint, trueTerm);
				programPointToState.put(tempProgramPoint, newState);
				arrOfProgPoints[i] = path.getSymbol(i).getTarget();
				if (i + 1 == path.length()) {
					// this is the last (accepting) state (the error location)
					pathPA.addState(false, true, newState);
				} else {
					pathPA.addState(false, false, newState);
				}
			}
			mPositionsToStates.add(i + 1, programPointToState.get(tempProgramPoint));
		}

		// Add the transitions
		for (int i = 0; i < path.length(); i++) {
			final IPredicate pred = mPositionsToStates.get(i);
			final IPredicate succ = mPositionsToStates.get(i + 1);
			if (path.isInternalPosition(i)) {
				pathPA.addInternalTransition(pred, path.getSymbol(i), succ);
			} else if (path.isCallPosition(i)) {
				pathPA.addCallTransition(pred, path.getSymbol(i), succ);
			} else if (path.isReturnPosition(i)) {
				final IPredicate hier = mPositionsToStates.get(path.getCallPosition(i));
				pathPA.addReturnTransition(pred, hier, path.getSymbol(i), succ);
			}
		}
		return pathPA;
	}

}
