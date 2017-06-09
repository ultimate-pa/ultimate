/*
 * Copyright (C) 2017 Jill Enke (enkei@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.fastupr.paraoct;

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

class OctagonSubstitution {
	private final TermVariable mVar;
	private final HashSet<OctagonSubstitutionTerm> mGreaterEqThan;
	private final HashSet<OctagonSubstitutionTerm> mLesserEqThan;

	protected OctagonSubstitution(TermVariable var) {
		mVar = var;
		mGreaterEqThan = new HashSet<>();
		mLesserEqThan = new HashSet<>();
	}

	void addSubstitution(OctTerm term) {
		if (term.getFirstVar().equals(mVar)) {
			addSubstitution(term, true);
		} else if (term.getSecondVar().equals(mVar)) {
			addSubstitution(term, false);
		}
	}

	void addSubstitution(OctTerm term, boolean first) {

		OctagonSubstitutionTerm subTerm;
		boolean greater = false;

		if (first) {
			if (term.isOneVar()) {
				subTerm = new OctagonSubstitutionTerm(term.getValue());
			} else {
				subTerm = new OctagonSubstitutionTerm(term.getValue(), term.getSecondVar(), term.isSecondNegative());
			}
			if (term.isFirstNegative()) {
				greater = true;
			}
		} else {
			subTerm = new OctagonSubstitutionTerm(term.getValue(), term.getFirstVar(), term.isFirstNegative());
			if (term.isSecondNegative()) {
				greater = true;
			}
		}

		addSubstitution(subTerm, greater);
	}

	void addSubstitution(OctagonSubstitutionTerm term, boolean greater) {
		if (greater) {
			mGreaterEqThan.add(term);
		} else {
			mLesserEqThan.add(term);
		}
	}

	HashSet<OctagonSubstitutionTerm> getGreaterSubsitutions() {
		return mGreaterEqThan;
	}

	HashSet<OctagonSubstitutionTerm> getLesserSubsitutions() {
		return mLesserEqThan;
	}

	@Override
	public String toString() {
		if (mGreaterEqThan.isEmpty() && mLesserEqThan.isEmpty()) {
			return " > Substitution for " + mVar.toString() + " empty. \n";
		}
		final StringBuilder sb = new StringBuilder(" > Substitution for " + mVar.toString() + ":\n");
		sb.append("Greater Equal Than: ");
		for (final OctagonSubstitutionTerm t : mGreaterEqThan) {
			sb.append(t.toString() + "; ");
		}
		sb.append("\nLesser Equal Than: ");
		for (final OctagonSubstitutionTerm t : mLesserEqThan) {
			sb.append(t.toString() + "; ");
		}
		sb.append("\n");
		return sb.toString();
	}

}
