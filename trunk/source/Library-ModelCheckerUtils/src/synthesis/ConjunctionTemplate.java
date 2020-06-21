/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 */

package synthesis;

import java.util.ArrayList;
import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

public class ConjunctionTemplate extends Template {
	private ArrayList<RelationTemplate> mRelations;
	String mName;
	
	public ConjunctionTemplate(Script script, int conjuncts , int[] relation,
			Set<TermVariable> vars, String name) {
		mScript = script;
		mRelations = new ArrayList<RelationTemplate>();
		for(int i=0; i<conjuncts; i++){
			mName = name;
			RelationTemplate t = new RelationTemplate(script, relation[i], vars, name + "-" + i);
			mRelations.add(t);
			if (i==0) {
				mTerm = t.getTerm();
			} else {
				mTerm = mScript.term("and", mTerm, t.getTerm());
			}
		}
	}
}
