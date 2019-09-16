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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.clauses;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.DawgFactory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.dawgs.dawgstates.DawgState;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackEntry;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.DecideStackPropagatedLiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.partialmodel.GroundPropagationInfo;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class UnitPropagationData {

	private final List<GroundPropagationInfo> mGroundPropagations;
	private final List<DecideStackEntry> mQuantifiedPropagations;

	public UnitPropagationData(
			final EprClause clause, final DawgState<ApplicationTerm, Integer> clauseDawg,
			final DawgFactory<ApplicationTerm, TermVariable> dawgFactory) {

		final List<GroundPropagationInfo> groundPropagations = new ArrayList<>();
		final List<DecideStackEntry> quantifiedPropagations = new ArrayList<>();

		for (int i = 0; i < clause.getLiterals().size(); i++) {
			final ClauseLiteral cl = clause.getLiterals().get(i);
			final int litNr = i;
			final DawgState<ApplicationTerm, Boolean> unitPoints =
					dawgFactory.createMapped(clauseDawg, status -> status == litNr);
			assert unitPoints.isTotal();
			if (DawgFactory.isEmpty(unitPoints)) {
				continue;
			}
			if (cl instanceof ClauseEprLiteral) {
				final ClauseEprLiteral cel = (ClauseEprLiteral) cl;
				final DecideStackPropagatedLiteral dspl = new DecideStackPropagatedLiteral(cel, unitPoints);
				quantifiedPropagations.add(dspl);
			} else {
				final ClauseDpllLiteral cdl = (ClauseDpllLiteral) cl;
				groundPropagations.add(new GroundPropagationInfo(cdl, unitPoints));
			}
		}

		mQuantifiedPropagations = Collections.unmodifiableList(quantifiedPropagations);
		mGroundPropagations = Collections.unmodifiableList(groundPropagations);
	}

	public List<DecideStackEntry> getQuantifiedPropagations() {
		return mQuantifiedPropagations;
	}

	public List<GroundPropagationInfo> getGroundPropagations() {
		return mGroundPropagations;
	}
}
