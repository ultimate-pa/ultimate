package de.uni_freiburg.informatik.ultimate.boogie;

import de.uni_freiburg.informatik.ultimate.core.model.models.IType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;

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
