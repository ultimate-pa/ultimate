/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 */

package synthesis;

import java.util.ArrayList;
import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import synthesis.ConjunctionTemplate;

public class DisjunctionTemplate extends Template {
	ArrayList<ConjunctionTemplate> mDisjunctions;
	String mName;
	public DisjunctionTemplate(Script script, int disjuncts, int[] conjuncts , int[][] relation,
			Set<TermVariable> vars, String name) {
		mScript = script;
		mName = name;
		mDisjunctions = new ArrayList<ConjunctionTemplate>();
		for(int i=0; i < disjuncts; i++){
			ConjunctionTemplate t = new ConjunctionTemplate(script, conjuncts[i], relation[i], vars, name + "-" + i); 
			mDisjunctions.add(t);
			if (i==0) {
				mTerm = t.getTerm();
			} else {
				mTerm = mScript.term("or", mTerm, t.getTerm());
			}

		}
	}
}
