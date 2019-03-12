/*
 * Copyright (C) 2019 Luca Bruder (luca.bruder@gmx.de)
 *
 * This file is part of the ULTIMATE Library-ModelCheckerUtils library.
 *
 * The ULTIMATE Library-ModelCheckerUtils library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by the Free Software Foundation,
 * either version 3 of the License, or (at your option) any later version.
 *
 * The ULTIMATE Library-ModelCheckerUtils library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-ModelCheckerUtils library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-ModelCheckerUtils library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-ModelCheckerUtils library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.mapelim.monniaux;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

/**
 *
 * @author Luca Bruder (luca.bruder@gmx.de)
 *
 */
final class StoreSelectEqualityCollector extends TermTransformer {

	final Set<Term> mStoreTerms = new HashSet<>();
	final Set<Term> mSelectTerms = new HashSet<>();
	final Set<Term> mEqualityTerms = new HashSet<>();

	@Override
	protected void convert(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm aterm = (ApplicationTerm) term;
			final String funName = aterm.getFunction().getName();
			if (funName.equals("store")) {
				// It's a store term
				mStoreTerms.add(aterm);
			} else if (funName.equals("select")) {
				// It's a select term
				mSelectTerms.add(aterm);
			} else if (funName.equals("=")) {
				// It's an equality term
				mEqualityTerms.add(term);
			}
		}
		super.convert(term);
	}

	protected boolean isEmpty() {
		return mSelectTerms.isEmpty() && mStoreTerms.isEmpty() && mEqualityTerms.isEmpty();
	}
}