package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieLocation;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability.AuxStatementContainer.StRecExpr;

public class AuxStatementContainer {
	public enum StRecExpr {
		DECL_VAR, ASSIGN_VAR, IF_ST;
	}
	
	private Map<String, AuxStatement> sreMap;
	private Set<String> statements;
	
	public AuxStatementContainer() {
		sreMap = new HashMap<>();
	}
	
	public AuxStatementContainer(AuxStatementContainer auxStatement) {
		sreMap = auxStatement.getSreMap();
	}
	
	public List<Statement> getStatements(StRecExpr stRecExpr) {
		List<Statement> statList = new ArrayList<>();
		for(AuxStatement auxStatement : sreMap.values()) {
			Statement s = auxStatement.getStatement(stRecExpr);
			if(s != null) {
				statList.add(s);
			}
		}
		return statList;
	}
	
	public Set<String> getRelatedVariableForInstance(Object object) {
		Set<String> relatedVariables = new HashSet<>();
		for(Map.Entry<String, AuxStatement> entry : sreMap.entrySet()) {
			if(entry.getValue().getClass().getName().equals(object.getClass().getName())) {
				relatedVariables.add(entry.getKey());
			}
		}
		return relatedVariables;
	}
	
	public Set<Statement> setBoogieLocationForInstance(Object object, StRecExpr stRecExpr, final BoogieLocation bl) {
		Set<Statement> statements = new HashSet<>();
		for(Map.Entry<String, AuxStatement> entry : sreMap.entrySet()) {
			if(entry.getValue().getClass().getName().equals(object.getClass().getName())) {
				Statement statement = entry.getValue().getStatement(stRecExpr);
				if(statement != null) {
					statement.setLoc(bl);
				}
				statements.add(statement);
			}
		}
		return statements;
	}
	
	public AuxStatement addAuxStatement(String variable, AuxStatement auxStatement) {
		if(sreMap == null) {
			sreMap = new HashMap<>();
		}
		sreMap.put(variable, auxStatement);
		return auxStatement;
	}
	
	public Map<String, AuxStatement> getSreMap() {
		return sreMap;
	}

	public void setSreMap(Map<String, AuxStatement> sreMap) {
		this.sreMap = sreMap;
	}

	public Set<String> getStatements() {
		return statements;
	}

	public void setStatements(Set<String> statements) {
		this.statements = statements;
	}
}
