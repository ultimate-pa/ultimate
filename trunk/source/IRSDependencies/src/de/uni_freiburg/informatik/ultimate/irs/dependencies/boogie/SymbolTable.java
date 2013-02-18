package de.uni_freiburg.informatik.ultimate.irs.dependencies.boogie;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.model.IType;

public class SymbolTable
{
	protected HashMap<String, HashMap<String, CompleteBoogieVar>> mScopes;
	protected static final String sGlobalScopeIdentifier = "global";

	public SymbolTable()
	{
		mScopes = new HashMap<>();
	}

	void addLocalVariable(String identifier, String procedure, IType type)
	{
		if (procedure.equals(sGlobalScopeIdentifier)) {
			throw new IllegalArgumentException(
					"Procedure name is equal to global scope identifier "
							+ sGlobalScopeIdentifier);
		}
		CompleteBoogieVar var = new CompleteBoogieVar(identifier, procedure,
				type);
		HashMap<String, CompleteBoogieVar> scope;
		if (mScopes.containsKey(procedure)) {
			scope = mScopes.get(procedure);
		}
		else {
			scope = new HashMap<>();
			mScopes.put(procedure, scope);
		}
		scope.put(identifier, var);
	}

	void addGlobalVariable(String identifier, IType type)
	{
		CompleteBoogieVar var = new CompleteBoogieVar(identifier, null, type);
		HashMap<String, CompleteBoogieVar> scope;
		if (mScopes.containsKey(sGlobalScopeIdentifier)) {
			scope = mScopes.get(sGlobalScopeIdentifier);
		}
		else {
			scope = new HashMap<>();
			mScopes.put(sGlobalScopeIdentifier, scope);
		}
		scope.put(identifier, var);
	}

	public CompleteBoogieVar getVariable(String variableName,
			String procedureName)
	{
		HashMap<String, CompleteBoogieVar> scope;
		if (procedureName == null) {
			if (mScopes.containsKey(sGlobalScopeIdentifier)) {
				scope = mScopes.get(sGlobalScopeIdentifier);
			}
			else {
				return null;
			}
		}
		else {
			if (mScopes.containsKey(procedureName)) {
				scope = mScopes.get(procedureName);
			}
			else {
				return null;
			}
		}
		if (scope.containsKey(variableName)) {
			return scope.get(variableName);
		}
		else if (procedureName != null) {
			return getVariable(variableName, null);
		}
		else {
			return null;
		}
	}
	
	public List<CompleteBoogieVar> getVariables(String procedureName){
		List<CompleteBoogieVar> rtrList = new LinkedList<>();
		HashMap<String, CompleteBoogieVar> scope;
		if (mScopes.containsKey(sGlobalScopeIdentifier)) {
			scope = mScopes.get(sGlobalScopeIdentifier);
			rtrList.addAll(scope.values());
		}
		
		if(procedureName !=null){
			if (mScopes.containsKey(procedureName)) {
				scope = mScopes.get(procedureName);
				for(CompleteBoogieVar var : scope.values()){
					for(int i=rtrList.size()-1;i>=0;--i){
						if(var.getIdentifier().equals(rtrList.get(i).getIdentifier())){
							rtrList.remove(i);
						}
					}
				}
				rtrList.addAll(scope.values());
			}
		}
		
		return rtrList;
	}

	@Override
	public String toString()
	{
		StringBuilder sb = new StringBuilder();
		sb.append("\n");
		for (Entry<String, HashMap<String, CompleteBoogieVar>> entry : mScopes
				.entrySet()) {
			if (entry.getKey().equals(sGlobalScopeIdentifier)) {
				sb.append("Global:\n");
			}
			else {
				sb.append("Procedure ");
				sb.append(entry.getKey());
				sb.append(":\n");
			}

			for (Entry<String, CompleteBoogieVar> innerEntry : entry.getValue()
					.entrySet()) {
				sb.append("Name is \"");
				sb.append(innerEntry.getKey());
				sb.append("\", CompleteBoogieVar is ");
				sb.append(innerEntry.getValue());
				sb.append("\n");
			}
		}
		return sb.toString();
	}

}
