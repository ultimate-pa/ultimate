/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.List;

/**
 * Interface for automata runs.<br>
 * A run is a sequence of states corresponding to a word, i.e., a sequence of symbols.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @param <CC>
 *            state type TODO Christian 2017-02-05 Why do we need two types? The first one is not used!
 */
public interface IRun<LETTER, STATE, CC> {
	/**
	 * The word corresponding to the run.
	 *
	 * @return corresponding word
	 */
	Word<LETTER> getWord();

	/**
	 * The symbol of the corresponding word at the given position.<br>
	 * The result is identical to {@link #getWord()}.{@link Word#getSymbol(int) getSymbol(position)}.
	 *
	 * @param position
	 *            position in run/word
	 * @return symbol at the given position
	 */
	LETTER getSymbol(int position);

	/**
	 * The length of the run.<br>
	 * The result is identical to {@link #getWord()}.{@link Word#length() length()}.
	 *
	 * @return length of the run
	 */
	int getLength();

	/**
	 * @return The state sequence.
	 */
	List<CC> getStateSequence();
}
