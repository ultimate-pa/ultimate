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
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.EqualityProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCEquality;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.EprEqualityPredicate;

/**
 * Atom representing a ground equality.
 * Maybe this is just a dummy until it gets replaced by CCEquality in all places,
 * maybe we want not-shared ground equalities in the Epr theory --> not sure yet..
 *
 * Note that this does not extend EprEqualityAtom because that is assumed to represent
 * a quantified equality.
 *
 * @author Alexander Nutz
 *
 */
public class EprGroundEqualityAtom extends EprGroundPredicateAtom {

	private final Term mLhs;
	private final Term mRhs;
	private final List<ApplicationTerm> mPoint;


	public EprGroundEqualityAtom(final ApplicationTerm term, final int hash, final int assertionstacklevel,
			final EprEqualityPredicate eqPred, final SourceAnnotation source) {
		super(term, hash, assertionstacklevel, eqPred, source);
		assert term.getParameters().length == 2;
		mLhs = term.getParameters()[0];
		mRhs = term.getParameters()[1];

		mPoint =
				//								Arrays.stream(egea.getArguments()) // TODO Java 1.8
				//								.map(term -> term).collect(Collectors.toList());
				new ArrayList<>();
		for (int i = 0; i < this.getArguments().length; i++) {
			mPoint.add((ApplicationTerm) this.getArguments()[i]);
		}

	}

	@Override
	public Term getSMTFormula(final Theory smtTheory) {
		return getTerm();
	}

	public CCEquality getCCEquality(final Clausifier clausif) {
		final EqualityProxy eq = clausif.createEqualityProxy(mLhs, mRhs, getSourceAnnotation());
				// Safe since m_Term is neither true nor false
		if (eq == EqualityProxy.getTrueProxy()) {
			return null;
		}
		assert eq != EqualityProxy.getFalseProxy();
		final CCEquality resultAtom = (CCEquality) eq.getLiteral(getSourceAnnotation());

		assert resultAtom != null;
		return resultAtom;
	}

	public List<ApplicationTerm> getPoint() {
		return mPoint;
	}
}
