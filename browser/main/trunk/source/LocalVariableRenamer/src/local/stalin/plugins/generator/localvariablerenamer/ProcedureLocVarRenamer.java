package local.stalin.plugins.generator.localvariablerenamer;

import java.util.HashSet;
import java.util.Set;

/**
 * Obtain a copy of a procedure where the identifiers of all local variables
 * have been renamed. They are renamed by adding as suffix a separator and the
 * name of their procedure. 
 * @author heizmann@informatik.uni-freiburg.de
 */

public class ProcedureLocVarRenamer extends ProcedureWalker {
	
	private final String m_Separator;
	private String m_ProcedureName;
	private Set<String> m_Duplicates = new HashSet<String>();
	
	public ProcedureLocVarRenamer(String separator, Set<String> duplicates) {
		m_Separator = separator;
		m_Duplicates = duplicates;
	}
	
	void setProcedureName(String procedureName) {
		m_ProcedureName = procedureName;
	}
	
	
	@Override
	public String walkVariableIdentifier(String identifier) {
		if (m_Duplicates.contains(identifier)) {
			return identifier + m_Separator + m_ProcedureName;
		}
		else {
			return identifier;
		}
	}



}
