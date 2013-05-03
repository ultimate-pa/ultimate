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
public class BoogieVar implements Serializable {

	private static final long serialVersionUID = 103072739646531062L;
	private final String m_Identifier;
	private final String m_Procedure;
	private final IType m_IType;
	
	private final boolean m_Oldvar;
	
	private final int m_HashCode;
	
	/**
	 * TermVariable which represents this BoogieVar in SMT terms.
	 */
	private final TermVariable m_TermVariable;
	
	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar in
	 * closed SMT terms. 
	 */
	private final ApplicationTerm m_DefaultConstant;

	/**
	 * Constant (0-ary ApplicationTerm) which represents this BoogieVar if it
	 * occurs as next state variable in closed SMT which describe a transition. 
	 */
	private final ApplicationTerm m_PrimedConstant;

	
	public BoogieVar(String identifier, String procedure, IType iType, 
			boolean oldvar) {
		m_Identifier = identifier;
		m_Procedure = procedure;
		m_IType = iType;
		m_Oldvar = oldvar;
		assert (oldvar == false || m_Procedure == null);
		m_HashCode = computeHashCode();
		m_TermVariable = null;
		m_DefaultConstant = null;
		m_PrimedConstant = null;
	}
	
	
	public BoogieVar(String identifier, String procedure, IType iType, 
			boolean oldvar,
			TermVariable tv,
			ApplicationTerm defaultConstant,
			ApplicationTerm primedContant) {
		m_Identifier = identifier;
		m_Procedure = procedure;
		m_IType = iType;
		m_Oldvar = oldvar;
		assert (oldvar == false || m_Procedure == null);
		m_HashCode = computeHashCode();
		m_TermVariable = tv;
		m_DefaultConstant = defaultConstant;
		m_PrimedConstant = primedContant;
	}
	
	
	
	public String getIdentifier() {
		return m_Identifier;
	}
	public String getProcedure() {
		return m_Procedure;
	}
	public IType getIType() {
		return m_IType;
	}
	public boolean isGlobal() {
		return m_Procedure == null;
	}
	public boolean isOldvar() {
		return m_Oldvar;
	}
	
	public TermVariable getTermVariable() {
		assert m_TermVariable != null;
		return m_TermVariable;
	}


	public ApplicationTerm getDefaultConstant() {
		return m_DefaultConstant;
	}


	public ApplicationTerm getPrimedConstant() {
		return m_PrimedConstant;
	}
	
	
	/**
	 * Returns an identifier that is globally unique. If this is global non-old
	 * we return the identifier, if this is global oldvar we add old(.), if
	 * this is local we add the procedure name as prefix.
	 */
	public String getGloballyUniqueId() {
		if (isGlobal()) {
			if (isOldvar()) {
				return "old(" + m_Identifier+")";
			} else {
				return m_Identifier;
			}
		} else {
			return m_Procedure + "_" + m_Identifier;
		}
	}
	
	@Override
	public String toString() {
		return getGloballyUniqueId();
	}

	private int computeHashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_Identifier == null) ? 0 : m_Identifier.hashCode());
		result = prime * result + (m_Oldvar ? 1231 : 1237);
		result = prime * result
				+ ((m_Procedure == null) ? 0 : m_Procedure.hashCode());
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
		if (m_Identifier == null) {
			if (other.m_Identifier != null)
				return false;
		} else if (!m_Identifier.equals(other.m_Identifier))
			return false;
		if (m_Oldvar != other.m_Oldvar)
			return false;
		if (m_Procedure == null) {
			if (other.m_Procedure != null)
				return false;
		} else if (!m_Procedure.equals(other.m_Procedure))
			return false;
		return true;
	}
	

	

}
