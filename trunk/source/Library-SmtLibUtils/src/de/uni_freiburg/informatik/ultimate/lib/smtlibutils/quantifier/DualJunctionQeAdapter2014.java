/*
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
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

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Adapter that allows us to use the old
 * {@link XjunctPartialQuantifierElimination} in the new
 * {@link DualJunctionQuantifierElimination}. The development of the old
 * {@link XjunctPartialQuantifierElimination} started in around 2014, hence the
 * name of this class.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */

public class DualJunctionQeAdapter2014 extends DualJunctionQuantifierElimination {
	private final XjunctPartialQuantifierElimination mXjunctPqe;

	public DualJunctionQeAdapter2014(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final XjunctPartialQuantifierElimination xJunctPqe) {
		super(mgdScript, services);
		mXjunctPqe = xJunctPqe;
	}

	@Override
	public String getName() {
		return mXjunctPqe.getName();
	}

	@Override
	public String getAcronym() {
		return mXjunctPqe.getAcronym();
	}

	@Override
	public EliminationResult tryToEliminate(final EliminationTask et) {
		final Term[] dualJuncts = QuantifierUtils.getDualFiniteJuncts(et.getQuantifier(), et.getTerm());
		final Set<TermVariable> modifiableEliminateeSet = new LinkedHashSet<>(et.getEliminatees());
		final Term[] resultdualJuncts = mXjunctPqe.tryToEliminate(et.getQuantifier(), dualJuncts,
				modifiableEliminateeSet);
		final Term resultDualJunction = QuantifierUtils.applyDualFiniteConnective(mScript, et.getQuantifier(),
				resultdualJuncts);
		final EliminationTask resultEt = et.update(modifiableEliminateeSet, resultDualJunction);
		if (resultEt.getEliminatees().containsAll(et.getEliminatees())) {
			// no eliminatee has been removed
			return null;
		} else {
			return new EliminationResult(resultEt, Collections.emptySet());
		}
	}

}
