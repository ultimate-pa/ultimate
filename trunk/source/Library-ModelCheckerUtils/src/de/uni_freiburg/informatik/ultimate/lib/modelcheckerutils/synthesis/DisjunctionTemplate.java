/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 */

package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.synthesis;

import java.util.ArrayList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class DisjunctionTemplate extends Template {
	private final ArrayList<ConjunctionTemplate> mDisjunctions;
	private final String mName;

	public DisjunctionTemplate(final Script script, final int disjuncts, final int[] conjuncts, final int[][] relation,
			final Set<TermVariable> vars, final String name) {
		mScript = script;
		mName = name;
		mDisjunctions = new ArrayList<>();
		for (int i = 0; i < disjuncts; i++) {
			final ConjunctionTemplate t =
					new ConjunctionTemplate(script, conjuncts[i], relation[i], vars, name + "-" + i);
			mDisjunctions.add(t);
			if (i == 0) {
				mTerm = t.getTerm();
			} else {
				mTerm = mScript.term("or", mTerm, t.getTerm());
			}
		}
	}
}
