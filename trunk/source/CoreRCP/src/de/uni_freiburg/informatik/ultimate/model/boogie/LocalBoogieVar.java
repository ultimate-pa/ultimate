package de.uni_freiburg.informatik.ultimate.model.boogie;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IType;

/**
 * Variable in a boogie program. The procedure field of global variables is null.
 * Only global variables can be old variables. Two BoogieVars are equivalent if 
 * they have the same identifier, same procedure, same old-flag. Equivalence
 * does not depend on the IType. We expect that two equivalent BoogieVars with
 * different ITypes never occur in the same program. 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class LocalBoogieVar extends BoogieVar  implements Serializable {

	private static final long serialVersionUID = 103072739646531062L;
	private final String m_Procedure;
	
	private final int m_HashCode;
	
	
	public LocalBoogieVar(String identifier, String procedure, IType iType, 
			TermVariable tv,
			ApplicationTerm defaultConstant,
			ApplicationTerm primedContant) {
		super(identifier, iType, tv, defaultConstant, primedContant);
		m_Procedure = procedure;
		m_HashCode = computeHashCode();
	}
	
	
	/**
	 * Returns the procedure in which this variable was declared. If this a 
	 * global variable, then null is returned.
	 */
	@Override
	public String getProcedure() {
		return m_Procedure;
	}
	@Override
	public boolean isGlobal() {
		return false;
	}
	public boolean isOldvar() {
		return false;
	}
	
	private int computeHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((getIdentifier() == null) ? 0 : getIdentifier().hashCode());
		result = prime * result + (isOldvar() ? 1231 : 1237);
		result = prime * result
				+ ((getProcedure() == null) ? 0 : getProcedure().hashCode());
		return result;
	}

	@Override
	public int hashCode() {
		return m_HashCode;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		BoogieVar other = (BoogieVar) obj;
		if (getIdentifier() == null) {
			if (other.getIdentifier() != null)
				return false;
		} else if (!getIdentifier().equals(other.getIdentifier()))
			return false;
		if (isOldvar() != other.isOldvar())
			return false;
		if (getProcedure() == null) {
			if (other.getProcedure() != null)
				return false;
		} else if (!getProcedure().equals(other.getProcedure()))
			return false;
		return true;
	}
	

	

}
