package local.stalin.plugins.generator.localvariablerenamer;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import local.stalin.core.api.StalinServices;
import local.stalin.model.boogie.ast.Procedure;
import local.stalin.model.boogie.ast.VarList;
import local.stalin.model.boogie.ast.VariableDeclaration;

/**
 * Find all local variable identifiers that occur in more than one procedure.
 * @author heizmann@informatik.uni-freiburg.de
 */

public class FindDuplicateLocVar extends ProcedureWalker {
	
	private static Logger s_Logger = 
				StalinServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private String m_ProcedureName;
	private Set<String> m_localVariableIdentifiers = new HashSet<String>();
	private Map<String,String> m_FirstOccurence = new HashMap<String,String>();
	private Set<String> m_Duplicates = new HashSet<String>();
	
	Set<String> getDuplicates() {
		return m_Duplicates;
	}

	
	@Override
	public Procedure walkProcedure(Procedure proc) {
		//Compute the set of all identifiers of local variables this procedure
		m_localVariableIdentifiers.clear();
		for (VarList varList : proc.getInParams()) {
			String[] identifiers = varList.getIdentifiers();
			for (String identifier : identifiers) {
				m_localVariableIdentifiers.add(identifier);
			}			
		}
		for (VarList varList : proc.getOutParams()) {
			String[] identifiers = varList.getIdentifiers();
			for (String identifier : identifiers) {
				m_localVariableIdentifiers.add(identifier);
			}			
		}
		if (proc.getBody() != null) {
			VariableDeclaration[] varDecls = proc.getBody().getLocalVars();
			for(VariableDeclaration varDecl : varDecls) {
				for (VarList varList : varDecl.getVariables()) {
					String[] identifiers = varList.getIdentifiers();
					for (String identifier : identifiers) {
						m_localVariableIdentifiers.add(identifier);
					}			
				}
			}
		}
		return super.walkProcedure(proc);
	}

	
	@Override
	public String walkVariableIdentifier(String identifier) {
		if (m_Duplicates.contains(identifier)) {
			return super.walkVariableIdentifier(identifier);
		}
		if (m_localVariableIdentifiers.contains(identifier)) {
			if (m_FirstOccurence.containsKey(identifier) && 
					!m_ProcedureName.equals(m_FirstOccurence.get(identifier))) {
				m_Duplicates.add(identifier);
				s_Logger.debug("Variable "+identifier+" occurs not only in " +
						"procedure "+ m_FirstOccurence.get(identifier)+ " but" +
								" also in procedure "+ m_ProcedureName);
			}
			else {
				m_FirstOccurence.put(identifier, m_ProcedureName);
			}
		}
		return super.walkVariableIdentifier(identifier);
	}


	void setProcedureName(String procedureName) {
		m_ProcedureName = procedureName;
	}



}
