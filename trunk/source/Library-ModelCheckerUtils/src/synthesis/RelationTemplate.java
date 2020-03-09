/*
 * Copyright (C) 2020 Daniel Fertmann (fertmand@cs.uni-freiburg.de)
 * Copyright (C) 2020 Jan Oreans (oreansj@cs.uni-freiburg.de)
 * Copyright (C) 2020 University of Freiburg
 */

package synthesis;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class RelationTemplate extends Template {
	Term mTerm;
	public RelationTemplate(int relation,
			Set<TermVariable> vars, String name) {
		int l = vars.size();
		int i = 0;
		for (TermVariable v : vars ){
		//	TermVariable a = new TermVariable()
			i++;
		}
	}
}
