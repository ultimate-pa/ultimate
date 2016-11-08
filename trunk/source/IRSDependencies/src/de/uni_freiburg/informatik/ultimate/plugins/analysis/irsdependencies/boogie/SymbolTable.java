/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.boogie;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;

public class SymbolTable
{
	protected HashMap<String, HashMap<String, CompleteBoogieVar>> mScopes;
	protected static final String sGlobalScopeIdentifier = "global";

	public SymbolTable()
	{
		mScopes = new HashMap<String, HashMap<String, CompleteBoogieVar>>();
	}

	void addLocalVariable(String identifier, String procedure, IBoogieType type)
	{
		if (procedure.equals(sGlobalScopeIdentifier)) {
			throw new IllegalArgumentException(
					"Procedure name is equal to global scope identifier "
							+ sGlobalScopeIdentifier);
		}
		final CompleteBoogieVar var = new CompleteBoogieVar(identifier, procedure,
				type);
		HashMap<String, CompleteBoogieVar> scope;
		if (mScopes.containsKey(procedure)) {
			scope = mScopes.get(procedure);
		}
		else {
			scope = new HashMap<String, CompleteBoogieVar>();
			mScopes.put(procedure, scope);
		}
		scope.put(identifier, var);
	}

	void addGlobalVariable(String identifier, IBoogieType type)
	{
		final CompleteBoogieVar var = new CompleteBoogieVar(identifier, null, type);
		HashMap<String, CompleteBoogieVar> scope;
		if (mScopes.containsKey(sGlobalScopeIdentifier)) {
			scope = mScopes.get(sGlobalScopeIdentifier);
		}
		else {
			scope = new HashMap<String, CompleteBoogieVar>();
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
		final List<CompleteBoogieVar> rtrList = new LinkedList<CompleteBoogieVar>();
		HashMap<String, CompleteBoogieVar> scope;
		if (mScopes.containsKey(sGlobalScopeIdentifier)) {
			scope = mScopes.get(sGlobalScopeIdentifier);
			rtrList.addAll(scope.values());
		}
		
		if(procedureName !=null){
			if (mScopes.containsKey(procedureName)) {
				scope = mScopes.get(procedureName);
				for(final CompleteBoogieVar var : scope.values()){
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
		final StringBuilder sb = new StringBuilder();
		sb.append("\n");
		for (final Entry<String, HashMap<String, CompleteBoogieVar>> entry : mScopes
				.entrySet()) {
			if (entry.getKey().equals(sGlobalScopeIdentifier)) {
				sb.append("Global:\n");
			}
			else {
				sb.append("Procedure ");
				sb.append(entry.getKey());
				sb.append(":\n");
			}

			for (final Entry<String, CompleteBoogieVar> innerEntry : entry.getValue()
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
