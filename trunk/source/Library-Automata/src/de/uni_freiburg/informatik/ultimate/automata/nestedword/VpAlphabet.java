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
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Visibly pushdown Alphabet. Alphabet consisting of three not necessarily disjoint sets. For visibly pushdown automata
 * a (disjoint) partition into internal, call, and return alphabets is necessary. For our NestedWordAutomata this
 * segmentation can increase the performance of operations but is not necessary.
 *
 * @author Matthias Heizmann
 * @param <LETTER>
 *            Type of the Objects that can be used as letters.
 */
public class VpAlphabet<LETTER> {
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
	public VpAlphabet(final Set<LETTER> internalAlphabet, final Set<LETTER> callAlphabet,
			final Set<LETTER> returnAlphabet) {
		mInternalAlphabet = internalAlphabet;
		mCallAlphabet = callAlphabet;
		mReturnAlphabet = returnAlphabet;
	}

	public VpAlphabet(final Set<LETTER> internalAlphabet) {
		mInternalAlphabet = internalAlphabet;
		mCallAlphabet = Collections.emptySet();
		mReturnAlphabet = Collections.emptySet();
	}

	/**
	 * Constructor for copy where symbols are replaced according to a given mapping.
	 *
	 */
	public VpAlphabet(final VpAlphabet<LETTER> vpAlphabet, final Map<LETTER, LETTER> mapping) {
		mInternalAlphabet = vpAlphabet.getInternalAlphabet().stream().map(mapping::get)
				.collect(Collectors.toSet());
		mCallAlphabet = vpAlphabet.getCallAlphabet().stream().map(mapping::get)
				.collect(Collectors.toSet());
		mReturnAlphabet = vpAlphabet.getReturnAlphabet().stream().map(mapping::get)
				.collect(Collectors.toSet());
	}


	/**
	 * @return Set of all letters that can occur as label of an internal transition.
	 *         <p>
	 *         The default definition of nested word automata does not allow separate alphabets for internal, call, and
	 *         return symbols. The default definition of visibly pushdown automata requires that all three alphabets are
	 *         disjoint. We deviate from both definitions. We allow separate alphabets but do not require that they are
	 *         disjoint.
	 */
	public Set<LETTER> getInternalAlphabet() {
		return mInternalAlphabet;
	}

	/**
	 * @return Set of all letters that can occur as label of a call transition.
	 * @see #getInternalAlphabet()
	 */
	public Set<LETTER> getCallAlphabet() {
		return mCallAlphabet;
	}

	/**
	 * @return Set of all letters that can occur as label of a return transition.
	 * @see #getInternalAlphabet()
	 */
	public Set<LETTER> getReturnAlphabet() {
		return mReturnAlphabet;
	}

	/**
	 * @return true iff <code>letter</code> is the label for any transition.
	 */
	public boolean containsAny(final LETTER letter) {
		return mInternalAlphabet.contains(letter) || mCallAlphabet.contains(letter) || mReturnAlphabet.contains(letter);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mCallAlphabet == null ? 0 : mCallAlphabet.hashCode());
		result = prime * result + (mInternalAlphabet == null ? 0 : mInternalAlphabet.hashCode());
		result = prime * result + (mReturnAlphabet == null ? 0 : mReturnAlphabet.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final VpAlphabet other = (VpAlphabet) obj;
		if (mCallAlphabet == null) {
			if (other.mCallAlphabet != null) {
				return false;
			}
		} else if (!mCallAlphabet.equals(other.mCallAlphabet)) {
			return false;
		}
		if (mInternalAlphabet == null) {
			if (other.mInternalAlphabet != null) {
				return false;
			}
		} else if (!mInternalAlphabet.equals(other.mInternalAlphabet)) {
			return false;
		}
		if (mReturnAlphabet == null) {
			if (other.mReturnAlphabet != null) {
				return false;
			}
		} else if (!mReturnAlphabet.equals(other.mReturnAlphabet)) {
			return false;
		}
		return true;
	}

}
