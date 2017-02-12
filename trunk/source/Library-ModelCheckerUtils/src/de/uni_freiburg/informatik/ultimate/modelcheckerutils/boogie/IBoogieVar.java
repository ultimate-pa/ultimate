
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IBoogieVar {

	String getGloballyUniqueId();

	ApplicationTerm getDefaultConstant();

	Sort getSort();

}
