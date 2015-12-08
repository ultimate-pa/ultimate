package de.uni_freiburg.informatik.ultimate.model.boogie;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.model.IType;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IBoogieVar {
	public String getIdentifier();

	public IType getIType();

	public ApplicationTerm getDefaultConstant();
}
