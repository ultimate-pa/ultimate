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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.automatondeltadebugger.factories;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Factory for {@link NestedWordAutomaton} objects.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class NestedWordAutomatonFactory<LETTER, STATE> extends INestedWordAutomatonFactory<LETTER, STATE> {
	private final IUltimateServiceProvider mServices;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param automaton
	 *            nested word automaton
	 */
	public NestedWordAutomatonFactory(final IUltimateServiceProvider services,
			final INestedWordAutomaton<LETTER, STATE> automaton) {
		super(automaton);
		mServices = services;
	}

	/**
	 * Casts the automaton interface to a concrete class.
	 *
	 * @param automaton
	 *            automaton interface
	 * @return cast automaton
	 */
	private NestedWordAutomaton<LETTER, STATE> getNwa(final INestedWordAutomaton<LETTER, STATE> automaton) {
		return (NestedWordAutomaton<LETTER, STATE>) automaton;
	}

	@Override
	protected INestedWordAutomaton<LETTER, STATE> createWithAlphabets(final Set<LETTER> internalAlphabet,
			final Set<LETTER> callAlphabet, final Set<LETTER> returnAlphabet) {
		return new NestedWordAutomaton<>(new AutomataLibraryServices(mServices),
				new VpAlphabet<>(internalAlphabet, callAlphabet, returnAlphabet), (IEmptyStackStateFactory<STATE>) mAutomaton.getStateFactory());
	}

	@Override
	public void addState(final INestedWordAutomaton<LETTER, STATE> automaton, final STATE state,
			final boolean isInitial, final boolean isFinal) {
		getNwa(automaton).addState(isInitial, isFinal, state);
	}

	@Override
	public void addInternalTransition(final INestedWordAutomaton<LETTER, STATE> automaton, final STATE pred,
			final LETTER letter, final STATE succ) {
		getNwa(automaton).addInternalTransition(pred, letter, succ);
	}

	@Override
	public void addCallTransition(final INestedWordAutomaton<LETTER, STATE> automaton, final STATE pred,
			final LETTER letter, final STATE succ) {
		getNwa(automaton).addCallTransition(pred, letter, succ);
	}

	@Override
	public void addReturnTransition(final INestedWordAutomaton<LETTER, STATE> automaton, final STATE pred,
			final STATE hier, final LETTER letter, final STATE succ) {
		getNwa(automaton).addReturnTransition(pred, hier, letter, succ);
	}
}
