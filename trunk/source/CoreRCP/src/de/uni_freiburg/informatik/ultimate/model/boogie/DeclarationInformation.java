package de.uni_freiburg.informatik.ultimate.model.boogie;

/**
 * The class is used to store information about where we can find the
 * declaration of an IdentifierExpression of a VariableLeftHandSide.
 * 
 * @author Matthias Heizmann
 */
public class DeclarationInformation {

	/**
	 * Defines where the declaration of a variable/constant is stored.
	 */
	public static enum StorageClass {
		/**
		 * All global variables and constants
		 */
		GLOBAL,
		/**
		 * "In" parameter of a function declaration or
		 * procedure declaration (with or without body/implementation)
		 */
		PROC_FUNC_INPARAM,
		/**
		 * "Out" parameter of function declaration or 
		 * procedure declaration (with or without body/implementation)
		 */
		PROC_FUNC_OUTPARAM,
		/**
		 * "In" parameter of a procedure implementation
		 */
		IMPLEMENTATION_INPARAM,
		/**
		 * "Out" parameter of a procedure implementation
		 */
		IMPLEMENTATION_OUTPARAM,
		/**
		 * All local variables and constants
		 */
		LOCAL,

		QUANTIFIED, IMPLEMENTATION,
		/**
		 * All procedure or function declarations
		 */
		PROC_FUNC
	}

	private final StorageClass m_StorageClass;
	private final String m_Procedure;

	public DeclarationInformation(StorageClass storageClass, String procedure) {
		super();
		assert (isValid(storageClass, procedure));
		this.m_StorageClass = storageClass;
		this.m_Procedure = procedure;
	}

	public StorageClass getStorageClass() {
		return m_StorageClass;
	}

	public String getProcedure() {
		return m_Procedure;
	}

	/**
	 * A DeclarationInformation is valid, if the procedure is non-null exactly
	 * if the StorageClass corresponds to a procedure.
	 */
	private boolean isValid(StorageClass storageClass, String procedure) {
		final boolean result;
		switch (storageClass) {
		case IMPLEMENTATION:
		case PROC_FUNC:
		case GLOBAL:
		case QUANTIFIED:
			result = (procedure == null);
			break;
		case PROC_FUNC_INPARAM:
		case PROC_FUNC_OUTPARAM:
		case IMPLEMENTATION_INPARAM:
		case IMPLEMENTATION_OUTPARAM:
		case LOCAL:
			result = (procedure != null);
			break;
		default:
			throw new AssertionError("unknown StorageClass");
		}
		return result;
	}

	@Override
	public String toString() {
		if (m_Procedure == null) {
			return m_StorageClass.toString();
		} else {
			return "<" + m_StorageClass.toString() + "," + m_Procedure + ">";
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result
				+ ((m_Procedure == null) ? 0 : m_Procedure.hashCode());
		result = prime * result
				+ ((m_StorageClass == null) ? 0 : m_StorageClass.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		DeclarationInformation other = (DeclarationInformation) obj;
		if (m_Procedure == null) {
			if (other.m_Procedure != null)
				return false;
		} else if (!m_Procedure.equals(other.m_Procedure))
			return false;
		if (m_StorageClass != other.m_StorageClass)
			return false;
		return true;
	}
	
	
}
