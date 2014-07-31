package de.uni_freiburg.informatik.ultimate.model.boogie;

import java.io.Serializable;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.IType;

/**
 * See comment in GlobalBoogieVar.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BoogieOldVar extends GlobalBoogieVar implements Serializable {

	private static final long serialVersionUID = 103072739646531062L;
	
	private BoogieVar m_NonOldVar;
	
	private final int m_HashCode;

	
	public BoogieOldVar(String identifier, IType iType, 
			boolean oldvar,
			TermVariable tv,
			ApplicationTerm defaultConstant,
			ApplicationTerm primedContant) {
		super(identifier, iType, tv, defaultConstant, primedContant);
		m_HashCode = computeHashCode();
	}
	
	public boolean isOldvar() {
		return true;
	}

	
	public BoogieVar getNonOldVar() {
		return m_NonOldVar;
	}


	public void setNonOldVar(BoogieNonOldVar nonOldVar) {
		m_NonOldVar = nonOldVar;
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
