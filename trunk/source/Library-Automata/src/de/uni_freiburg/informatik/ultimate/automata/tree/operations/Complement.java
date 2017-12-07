/*
 * Copyright (C) 2016 Mostafa M.A. (mostafa.amin93@gmail.com)
 * Copyright (C) 2014-2016 University of Freiburg
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.Collection;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;

/**
 * Complements a given treeAutomaton.
 * 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <LETTER>
 *            letter of the tree automaton.
 * @param <STATE>
 *            state of the tree automaton.
 */
public class Complement<LETTER extends IRankedLetter, STATE>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>>
		implements IOperation<LETTER, STATE, IStateFactory<STATE>> {

	private final ITreeAutomatonBU<LETTER, STATE> mTreeAutomaton;

	protected final ITreeAutomatonBU<LETTER, STATE> mResult;
	private final Collection<LETTER> mAlphabet;

	/***
	 * Constructor of the complement operator
	 * 
	 * @param services
	 * @param factory
	 * @param tree
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE>> Complement(
			final AutomataLibraryServices services, final SF factory, final ITreeAutomatonBU<LETTER, STATE> tree) {
		super(services);
		mAlphabet = new HashSet<>();
		mTreeAutomaton = new Totalize<>(mServices, factory, tree).getResult();

		mResult = computeResult(factory);
	}

	/***
	 * Constructor of the complement operator
	 * 
	 * @param services
	 * @param factory
	 * @param tree
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE>> Complement(
			final AutomataLibraryServices services, final SF factory, final ITreeAutomatonBU<LETTER, STATE> tree,
			final Collection<LETTER> alphabet) {
		super(services);
		mAlphabet = new HashSet<>();
		mAlphabet.addAll(alphabet);
		mTreeAutomaton = new Totalize<>(mServices, factory, tree, alphabet).getResult();
		mResult = computeResult(factory);
	}

	@Override
	public String startMessage() {
		return "Starting complementing";
	}

	@Override
	public String exitMessage() {
		return "Exiting complementing";
	}

	private <F extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE>> ITreeAutomatonBU<LETTER, STATE> computeResult(
			final F stateFactory) {
		mTreeAutomaton.complementFinals();
		return mTreeAutomaton;
	}

	@Override
	public ITreeAutomatonBU<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
}
