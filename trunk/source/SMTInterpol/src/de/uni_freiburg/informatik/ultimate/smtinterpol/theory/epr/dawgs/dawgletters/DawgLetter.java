/*
 * Copyright (C) 2016-2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016-2017 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgletters;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * A SimpleDawgLetter represents a set of LETTER. Its internal representation is a finite Set of letters or its
 * complement.
 *
 * @author Alexander Nutz, Jochen Hoenicke
 *
 * @param <LETTER>
 *            The letter type.
 */
public class DawgLetter<LETTER> {
	final DawgLetterFactory<LETTER> mDawgLetterFactory;
	DawgLetter<LETTER> mComplement;
	final Set<LETTER> mLetters;
	final Object mSortId;
	final boolean mIsComplemented;

	public DawgLetter(final DawgLetterFactory<LETTER> dlf, final Set<LETTER> letters, final Object sortId) {
		mDawgLetterFactory = dlf;
		mLetters = letters;
		mSortId = sortId;
		mIsComplemented = false;
	}

	public DawgLetter(final DawgLetter<LETTER> complement) {
		assert !complement.mIsComplemented;
		mDawgLetterFactory = complement.mDawgLetterFactory;
		mLetters = complement.mLetters;
		mSortId = complement.mSortId;
		mIsComplemented = true;
		mComplement = complement;
		complement.mComplement = this;
	}

	public Object getSortId() {
		return mSortId;
	}

	public final DawgLetter<LETTER> difference(final DawgLetter<LETTER> other) {
		return intersect(other.complement());
	}

	public DawgLetter<LETTER> complement() {
		if (mComplement == null) {
			mComplement = new DawgLetter<>(this);
		}
		return mComplement;
	}

	/**
	 * Compute a DawgLetter whose denotation is the intersection of the denotation of the given two DawgLetters.
	 *
	 * Note that this does not take into account equalities that may hold between LETTERs. E.g., {a}.intersect({b}) will
	 * yield the EmptyDawgLetter even if our current decide state says that a equals b.
	 *
	 * @param other
	 * @return
	 */
	public DawgLetter<LETTER> intersect(final DawgLetter<LETTER> other) {
		if (!mIsComplemented) {
			final HashSet<LETTER> intersection = new HashSet<>();
			for (final LETTER letter : mLetters) {
				if (other.matches(letter)) {
					intersection.add(letter);
				}
			}
			return mDawgLetterFactory.getSimpleDawgLetter(intersection, mSortId);
		} else if (!other.mIsComplemented) {
			final HashSet<LETTER> intersection = new HashSet<>();
			for (final LETTER letter : other.mLetters) {
				if (this.matches(letter)) {
					intersection.add(letter);
				}
			}
			return mDawgLetterFactory.getSimpleDawgLetter(intersection, mSortId);
		} else {
			final HashSet<LETTER> union = new HashSet<>();
			union.addAll(this.mLetters);
			union.addAll(other.mLetters);
			return mDawgLetterFactory.getSimpleComplementDawgLetter(union, mSortId);
		}
	}

	/**
	 * Check if ltr is in the set represented by this object.
	 *
	 * @param ltr
	 * @return
	 */
	public boolean matches(final LETTER ltr) {
		return mLetters.contains(ltr) ^ mIsComplemented;
	}

	public Set<LETTER> getLetters() {
		if (mIsComplemented) {
			final Set<LETTER> result = new HashSet<LETTER>(mDawgLetterFactory.getAllConstants(mSortId));
			result.removeAll(mLetters);
			return result;
		} else {
			return mLetters;
		}
	}

	public DawgLetter<LETTER> restrictToLetter(final LETTER selectLetter) {
		if (matches(selectLetter)) {
			return mDawgLetterFactory.getSimpleDawgLetter(Collections.singleton(selectLetter), mSortId);
		} else {
			return mDawgLetterFactory.getEmptyDawgLetter(mSortId);
		}
	}

	@Override
	public String toString() {
		return "DawgLetter: " + (mIsComplemented ? "not" : "") + mLetters;
	}

	public DawgLetter<LETTER> union(final DawgLetter<LETTER> other) {
		return this.complement().intersect(other.complement()).complement();
	}

	public boolean isDisjoint(final DawgLetter<LETTER> other) {
		if (!mIsComplemented) {
			for (final LETTER letter : mLetters) {
				if (other.matches(letter)) {
					return false;
				}
			}
			return true;
		} else if (!other.mIsComplemented) {
			for (final LETTER letter : other.mLetters) {
				if (this.matches(letter)) {
					return false;
				}
			}
			return true;
		} else {
			return false;
		}
	}

	public boolean isEmpty() {
		return !mIsComplemented && mLetters.size() == 0;
	}

	public boolean isUniversal() {
		return mIsComplemented && mLetters.size() == 0;
	}

	public Collection<LETTER> getRawLetters() {
		return mLetters;
	}

	public boolean isComplemented() {
		return mIsComplemented;
	}

	public boolean isSingleton() {
		return !mIsComplemented && mLetters.size() == 1;
	}
}
