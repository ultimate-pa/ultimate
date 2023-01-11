/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;


/**
 * Represents a task for quantifier elimination without quantifier alternation.
 * I.e., there in only a single kind of quantifier.
 * This class is very similar to ({@link QuantifiedFormula} but we want to have
 * this class to make its purpose more explicit
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class EliminationTask extends EliminationTaskSimple {
	private final Context mContext;

	public EliminationTask(final int quantifier, final Set<TermVariable> eliminatees, final Term term,
			final Context context) {
		super(quantifier, eliminatees, term, context.getBoundByAncestors());
		mContext = context;
	}

	public EliminationTask(final QuantifiedFormula quantifiedFormula, final Context context) {
		super(quantifiedFormula, context.getBoundByAncestors());
		mContext = context;
	}

	public Context getContext() {
		return mContext;
	}

	@Override
	public EliminationTask integrateNewEliminatees(final Collection<TermVariable> additionalEliminatees) {
		final Set<TermVariable> additionalOccuringEliminatees = QuantifierUtils.projectToFreeVars(additionalEliminatees,
				getTerm());
		final Set<TermVariable> resultEliminatees = new HashSet<TermVariable>(getEliminatees());
		final boolean modified = resultEliminatees.addAll(additionalOccuringEliminatees);
		if (modified) {
			return new EliminationTask(getQuantifier(), resultEliminatees, getTerm(), mContext);
		} else {
			return this;
		}
	}

	@Override
	public EliminationTask update(final Set<TermVariable> newEliminatees, final Term term) {
		return new EliminationTask(getQuantifier(), newEliminatees, term, mContext);
	}

	@Override
	public EliminationTask update(final Term term) {
		return new EliminationTask(getQuantifier(), getEliminatees(), term, mContext);
	}

	public Pair<Term, EliminationTask> makeTight(final IUltimateServiceProvider services,
			final ManagedScript mgdScript) {
		final Term[] dualJuncts = QuantifierUtils.getDualFiniteJuncts(getQuantifier(), getTerm());
		final List<Term> dualJunctsWithEliminatee = new ArrayList<>();
		final List<Term> dualJunctsWithoutEliminatee = new ArrayList<>();
		for (final Term dualJunct : dualJuncts) {
			if (DataStructureUtils.haveEmptyIntersection(getEliminatees(),
					new HashSet<>(Arrays.asList(dualJunct.getFreeVars())))) {
				dualJunctsWithoutEliminatee.add(dualJunct);
			} else {
				dualJunctsWithEliminatee.add(dualJunct);
			}
		}
		if (dualJunctsWithoutEliminatee.isEmpty()) {
			return null;
		} else {
			final Term dualJunctionWithoutEliminatee = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
					getQuantifier(), dualJunctsWithoutEliminatee);
			final Term dualJunctionWithEliminatee = QuantifierUtils.applyDualFiniteConnective(mgdScript.getScript(),
					getQuantifier(), dualJunctsWithEliminatee);

			final Context newContext = getContext().constructChildContextForConDis(services, mgdScript,
					((ApplicationTerm) getTerm()).getFunction(), dualJunctsWithoutEliminatee);
			return new Pair<>(dualJunctionWithoutEliminatee,
					new EliminationTask(getQuantifier(), getEliminatees(), dualJunctionWithEliminatee, newContext));
		}
	}

}