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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.atoms;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprPredicate;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class EprGroundPredicateAtom extends EprPredicateAtom {
	List<ApplicationTerm> mArgumentsAsWord;
	int mStackPosition;

	public EprGroundPredicateAtom(final ApplicationTerm term, final int hash, final int assertionstacklevel,
			final EprPredicate pred, final SourceAnnotation source) {
		super(term, hash, assertionstacklevel, pred, source);
		assert term.getFreeVars().length == 0 : "trying to create a ground atom from a non-ground term";
		mArgumentsAsWord = new ArrayList<>(getArguments().length);
		for (final Term arg : getArguments()) {
			mArgumentsAsWord.add((ApplicationTerm) arg);
		}
		mStackPosition = -1;
	}

	public boolean isOnEprStack() {
		return mStackPosition >= 0;
	}

	public int getEprStackPosition() {
		return mStackPosition;
	}

	public List<ApplicationTerm> getArgumentsAsWord() {
		return mArgumentsAsWord;
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory) {
		return getTerm();
	}

	public void setStackPosition(int pos) {
		mStackPosition = pos;
	}
}
