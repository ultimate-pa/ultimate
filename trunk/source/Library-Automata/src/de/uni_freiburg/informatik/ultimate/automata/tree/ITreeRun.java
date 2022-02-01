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
package de.uni_freiburg.informatik.ultimate.automata.tree;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISemanticReducerFactory;

/**
 *
 * @author Mostafa M.A. (mostafa.amin93@gmail.com)
 *
 * @param <LETTER> symbol
 * @param <STATE> state
 */
public interface ITreeRun<LETTER extends IRankedLetter, STATE> {

	/***
	 * Get an automaton representation of the tree run.
	 * @return
	 */
	ITreeAutomatonBU<LETTER, STATE> getAutomaton();

	/***
	 * Get an interpolant automaton representation of the tree run.
	 * @param factory
	 * @return
	 */
	<SF extends ISemanticReducerFactory<STATE, LETTER>> InterpolantTreeAutomatonBU<LETTER, STATE> getInterpolantAutomaton(final SF factory);

	/***
	 * Get the tree representation of the tree run
	 * @return
	 */
	Tree<LETTER> getTree();

	/***
	 * Get the root state
	 * @return
	 */
	STATE getRoot();

	/***
	 * Get the root symbol
	 * @return
	 */
	LETTER getRootSymbol();
}