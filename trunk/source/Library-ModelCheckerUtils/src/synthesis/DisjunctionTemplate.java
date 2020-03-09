/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 */

package synthesis;

import java.util.Set;
import java.util.TreeSet;

import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import synthesis.ConjunctionTemplate;

public class DisjunctionTemplate extends Template {
	Set<ConjunctionTemplate> mDisjunctions;
	public DisjunctionTemplate(int disjuncts, int[] conjuncts , int[][] relation,
			Set<TermVariable> vars, String name) {
		mDisjunctions = new TreeSet<ConjunctionTemplate>();
		for(int i=0; i < disjuncts; i++){
			//TODO change name
			ConjunctionTemplate t = new ConjunctionTemplate(conjuncts[i], relation[i], vars, name); 
			mDisjunctions.add(t);
		}
	}
}
