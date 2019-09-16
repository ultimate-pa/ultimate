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

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprTheorySettings;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.NestedMap2;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <COLNAMES>
 */
public class DawgLetterFactory<LETTER> {
	private final NestedMap2<Object, Set<LETTER>, DawgLetter<LETTER>> mSortToLettersToSimpleDawgLetter =
			new NestedMap2<Object, Set<LETTER>, DawgLetter<LETTER>>();
	private final DawgFactory<LETTER, ?> mDawgFactory;


	public DawgLetterFactory(final DawgFactory<LETTER, ?> dawgFactory) {
		mDawgFactory = dawgFactory;
	}

	public DawgLetter<LETTER> getSingletonSetDawgLetter(final LETTER element, final Object sortId) {
		return getSimpleDawgLetter(Collections.singleton(element), sortId);
	}

	public DawgLetter<LETTER> getUniversalDawgLetter(final Object sortId) {
		return getSimpleComplementDawgLetter(Collections.emptySet(), sortId);
	}

	public DawgLetter<LETTER> getEmptyDawgLetter(final Object sortId) {
		return getSimpleDawgLetter(Collections.emptySet(), sortId);
	}


	public Set<LETTER> getAllConstants(final Object sortId) {
		final Set<LETTER> result = mDawgFactory.getAllConstants(sortId);
		assert result != null;
		return result;
	}

	public DawgLetter<LETTER> getSimpleDawgLetter(Set<LETTER> letters, final Object sortId) {
		if (letters.isEmpty()) {
			letters = Collections.emptySet();
		}
		DawgLetter<LETTER> result = mSortToLettersToSimpleDawgLetter.get(sortId, letters);
		if (result == null) {
			result = new DawgLetter<LETTER>(this, letters, sortId);
			mSortToLettersToSimpleDawgLetter.put(sortId, letters, result);
		}
		return result;
	}

	public DawgLetter<LETTER> getSimpleComplementDawgLetter(final Set<LETTER> letters, final Object sortId) {
		return getSimpleDawgLetter(letters, sortId).complement();
	}

	public boolean useSimpleDawgLetters() {
		return EprTheorySettings.UseSimpleDawgLetters;
	}
}
