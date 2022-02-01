/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
/**
 * This package provides a framework for the constraint-based synthesis of
 * safety invariants, ranking functions, danger invariants, recurrence sets,
 * etc.
 *
 * @author Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Jan Oreans (oreansj@cs.uni-freiburg.de)
 *
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.synthesis;

import java.util.ArrayList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ConjunctionTemplate extends Template {
	private final ArrayList<RelationTemplate> mRelations;
	private final String mName;

	public ConjunctionTemplate(final Script script, final int conjuncts, final int[] relation,
			final Set<TermVariable> vars, final String name) {
		mScript = script;
		mRelations = new ArrayList<>();
		mName = name;

		for (int i = 0; i < conjuncts; i++) {
			final RelationTemplate t = new RelationTemplate(script, relation[i], vars, name + "-" + i);
			mRelations.add(t);
			if (i == 0) {
				mTerm = t.getTerm();
			} else {
				mTerm = mScript.term("and", mTerm, t.getTerm());
			}
		}
	}
}
