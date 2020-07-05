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
