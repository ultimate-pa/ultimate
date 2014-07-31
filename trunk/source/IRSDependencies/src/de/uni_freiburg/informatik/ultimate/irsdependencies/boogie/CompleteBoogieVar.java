package de.uni_freiburg.informatik.ultimate.irsdependencies.boogie;

import de.uni_freiburg.informatik.ultimate.model.IType;

/**
 * Class is used by Daniel for debugging symbol table. Orignially this was
 * a subclass of BoogieVar
 *
 *
 */
public class CompleteBoogieVar
{
	private static final long serialVersionUID = -7848336493120723097L;

	private final String m_Identifier;
	private final String m_Procedure;
	private final IType m_IType;
	
	private final boolean m_Oldvar;
	
	private final int m_HashCode;
	
	
	public CompleteBoogieVar(String identifier, String procedure, IType iType) {
		m_Identifier = identifier;
		m_Procedure = procedure;
		m_IType = iType;
		m_Oldvar = false;
		m_HashCode = computeHashCode();
	}
	

	
	public String getIdentifier() {
		return m_Identifier;
	}
	
	/**
	 * Returns the procedure in which this variable was declared. If this a 
	 * global variable, then null is returned.
	 */
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
		CompleteBoogieVar other = (CompleteBoogieVar) obj;
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
