package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.model.IType;


/**
 * Constant in a Boogie program.  
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BoogieConst {
	private final String m_Identifier;
	private final IType m_IType;
	
	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar in
	 * closed SMT terms. 
	 */
	private final ApplicationTerm m_SmtConstant;

	
	
	public BoogieConst(String identifier, IType iType,
			ApplicationTerm smtConstant) {
		m_Identifier = identifier;
		m_IType = iType;
		m_SmtConstant = smtConstant;
	}
	
	
	public String getIdentifier() {
		return m_Identifier;
	}

	public IType getIType() {
		return m_IType;
	}


	public ApplicationTerm getSmtConstant() {
		return m_SmtConstant;
	}


	@Override
	public int hashCode() {
		return m_Identifier.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		BoogieConst other = (BoogieConst) obj;
		if (m_SmtConstant == null) {
			if (other.m_SmtConstant != null)
				return false;
		} else if (!m_SmtConstant.equals(other.m_SmtConstant))
			return false;
		if (m_IType == null) {
			if (other.m_IType != null)
				return false;
		} else if (!m_IType.equals(other.m_IType))
			return false;
		if (m_Identifier == null) {
			if (other.m_Identifier != null)
				return false;
		} else if (!m_Identifier.equals(other.m_Identifier))
			return false;
		return true;
	}
}
