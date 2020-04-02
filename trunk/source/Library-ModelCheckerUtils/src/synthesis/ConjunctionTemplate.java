/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 */

package synthesis;

import java.util.ArrayList;
import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ConjunctionTemplate extends Template {
	private ArrayList<RelationTemplate> mRelations;
	String mName;
	
	public ConjunctionTemplate(int conjuncts , int[] relation,
			Set<TermVariable> vars, String name) {
		mRelations = new ArrayList<RelationTemplate>();
		for(int i=0; i<conjuncts; i++){
			mName = name;
			RelationTemplate t = new RelationTemplate(relation[i], vars, name + "-" + i);
			mRelations.add(t);
		}
	}
}
