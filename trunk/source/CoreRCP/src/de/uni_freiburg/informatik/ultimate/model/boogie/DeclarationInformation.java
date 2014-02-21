package de.uni_freiburg.informatik.ultimate.model.boogie;


/**
 * The class is used to store information about where we can find the 
 * declaration of an IdentifierExpression of a VariableLeftHandSide.  
 * @author Matthias Heizmann
 */
public class DeclarationInformation {
	
	/**
	 * Defines where the declaration of a variable/constant is stored. 
	 */
	public static enum StorageClass { GLOBAL, PROC_INPARAM, PROC_OUTPARAM, 
		FUNC_INPARAM, FUNC_OUTPARAM, LOCAL, QUANTIFIED }
	
	private final StorageClass m_StorageClass;
	private final String m_Procedure;
	public DeclarationInformation(StorageClass storageClass,
			String procedure) {
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
		case FUNC_INPARAM:
			result = (procedure == null);
			break;
		case FUNC_OUTPARAM:
			result = (procedure == null);
			break;
		case GLOBAL:
			result = (procedure == null);
			break;
		case LOCAL:
			result = (procedure != null);
			break;
		case PROC_INPARAM:
			result = (procedure != null);
			break;
		case PROC_OUTPARAM:
			result = (procedure != null);
			break;
		case QUANTIFIED:
			result = (procedure == null);
			break;
		default:
			throw new AssertionError("unknown StorageClass");
		}
		return result;
	}
}
