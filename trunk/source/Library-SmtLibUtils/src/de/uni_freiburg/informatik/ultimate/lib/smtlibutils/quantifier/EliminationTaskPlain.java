/*
 * Copyright (C) 2019 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier;


import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.quantifier.arrays.ElimStorePlain;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Special Elimination Task for {@link ElimStorePlain}.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @deprecated {@link ElimStorePlain} is outdated and only kept to compare old
 *             and new quantifier elimination for arrays.
 *
 */
@Deprecated
public class EliminationTaskPlain extends EliminationTaskSimple {
	private final Term mContext;

	public EliminationTaskPlain(final int quantifier, final Set<TermVariable> eliminatees, final Term term,
			final Set<TermVariable> bannedForDivCapture, final Term context) {
		super(quantifier, eliminatees, term, bannedForDivCapture);
		mContext = context;
	}

	public EliminationTaskPlain(final int quantifier, final Set<TermVariable> eliminatees, final Term term,
			final Term context) {
		super(quantifier, eliminatees, term);
		mContext = context;
	}

	public EliminationTaskPlain(final QuantifiedFormula quantifiedFormula,
			final Set<TermVariable> bannedForDivCapture, final Term context) {
		super(quantifiedFormula, bannedForDivCapture);
		mContext = context;
	}


	public Term getContext() {
		return mContext;
	}


	@Override
	public EliminationTaskPlain integrateNewEliminatees(final Collection<TermVariable> additionalEliminatees) {
		final Set<TermVariable> additionalOccuringEliminatees = QuantifierUtils.projectToFreeVars(additionalEliminatees,
				getTerm());
		final Set<TermVariable> resultEliminatees = new HashSet<TermVariable>(getEliminatees());
		final boolean modified = resultEliminatees.addAll(additionalOccuringEliminatees);
		if (modified) {
			return new EliminationTaskPlain(getQuantifier(), resultEliminatees, getTerm(), getBoundByAncestors(),
					mContext);
		} else {
			return this;
		}
	}

	@Override
	public EliminationTaskPlain update(final Set<TermVariable> newEliminatees, final Term term) {
		return new EliminationTaskPlain(getQuantifier(), newEliminatees, term, getBoundByAncestors(), mContext);
	}

	@Override
	public EliminationTaskPlain update(final Term term) {
		return new EliminationTaskPlain(getQuantifier(), getEliminatees(), term, getBoundByAncestors(), mContext);
	}

}