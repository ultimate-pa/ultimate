package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface INonrelationalValue<V extends INonrelationalValue<V>> {

	V copy();
	
	boolean isBottom();
	
	V intersect (V other);
	
	V merge (V other);
	
	boolean isEqualTo(V other);
	
	Term getTerm(final Script script, final Sort sort, final Term var);
	
	boolean isContainedIn(V otherValue);
}
