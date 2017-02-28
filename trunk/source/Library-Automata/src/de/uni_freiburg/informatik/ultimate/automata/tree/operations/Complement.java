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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;

/**
 * Complements a given treeAutomaton.
 * 
 * @author mostafa (mostafa.amin93@gmail.com)
 *
 * @param <R>
 *            letter of the tree automaton.
 * @param <S>
 *            state of the tree automaton.
 */
public class Complement<R, S> implements IOperation<R, S, IStateFactory<S>> {

	private final ITreeAutomatonBU<R, S> mTreeAutomaton;

	protected final ITreeAutomatonBU<R, S> mResult;
	private final AutomataLibraryServices mServices;

	/***
	 * Constructor of the compkement operator
	 * @param services
	 * @param factory
	 * @param tree
	 */
	public <F extends IMergeStateFactory<S> & IEmptyStackStateFactory<S>> Complement(
			final AutomataLibraryServices services, final F factory,
			final ITreeAutomatonBU<R, S> tree) {
		mServices = services;
		mTreeAutomaton = tree;

		mResult = computeResult(factory);
	}

	@Override
	public String operationName() {
		return "Complement";
	}

	@Override
	public String startMessage() {
		return "Starting complementing";
	}

	@Override
	public String exitMessage() {
		return "Exiting complementing";
	}

	private <F extends IMergeStateFactory<S> & IEmptyStackStateFactory<S>> ITreeAutomatonBU<R, S>
			computeResult(final F stateFactory) {
		final Determinize<R, S> op = new Determinize<>(mServices, stateFactory, mTreeAutomaton);
		final TreeAutomatonBU<R, S> res = (TreeAutomatonBU<R, S>) op.getResult();
		res.complementFinals();
		final Minimize<R, S> mini = new Minimize<>(mServices, stateFactory, res);
		return mini.getResult();
	}

	@Override
	public ITreeAutomatonBU<R, S> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<S> stateFactory) throws AutomataLibraryException {
		// TODO implement a meaningful check
		return true;
	}
}
