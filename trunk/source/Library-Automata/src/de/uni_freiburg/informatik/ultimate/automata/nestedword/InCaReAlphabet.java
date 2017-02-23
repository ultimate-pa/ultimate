/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;

/**
 * Alphabet consisting of three not necessarily disjoint sets.
 * For visibly pushdown automata a (disjoint) partition into internal, call, and
 * return alphabets is necessary. For our NestedWordAutomata this segmentation
 * can increase the performance of operations but is not necessary.
 * 
 * @author Matthias Heizmann
 * @param <LETTER>
 *            Type of the Objects that can be used as letters.
 */
public class InCaReAlphabet<LETTER> {
	private final Set<LETTER> mInternalAlphabet;
	private final Set<LETTER> mCallAlphabet;
	private final Set<LETTER> mReturnAlphabet;

	/**
	 * Constructor with direct passing of alphabets.
	 * 
	 * @param internalAlphabet
	 *            internal alphabet
	 * @param callAlphabet
	 *            call alphabet
	 * @param returnAlphabet
	 *            return alphabet
	 */
	public InCaReAlphabet(final Set<LETTER> internalAlphabet, final Set<LETTER> callAlphabet,
			final Set<LETTER> returnAlphabet) {
		mInternalAlphabet = internalAlphabet;
		mCallAlphabet = callAlphabet;
		mReturnAlphabet = returnAlphabet;
	}

	/**
	 * Constructor which takes the alphabets from an automaton.
	 * 
	 * @param automaton
	 *            automaton
	 */
	public InCaReAlphabet(final IAutomaton<LETTER, ?> automaton) {
		if (automaton instanceof INestedWordAutomatonSimple) {
			final INestedWordAutomatonSimple<LETTER, ?> nwa = (INestedWordAutomatonSimple<LETTER, ?>) automaton;
			mInternalAlphabet = nwa.getInternalAlphabet();
			mCallAlphabet = nwa.getCallAlphabet();
			mReturnAlphabet = nwa.getReturnAlphabet();
		} else {
			mInternalAlphabet = automaton.getAlphabet();
			mCallAlphabet = Collections.emptySet();
			mReturnAlphabet = Collections.emptySet();
		}
	}

	public Set<LETTER> getInternalAlphabet() {
		return mInternalAlphabet;
	}

	public Set<LETTER> getCallAlphabet() {
		return mCallAlphabet;
	}

	public Set<LETTER> getReturnAlphabet() {
		return mReturnAlphabet;
	}
}
