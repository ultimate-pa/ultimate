
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IBoogieVar {
	String getIdentifier();

	IBoogieType getIType();

	ApplicationTerm getDefaultConstant();
}
