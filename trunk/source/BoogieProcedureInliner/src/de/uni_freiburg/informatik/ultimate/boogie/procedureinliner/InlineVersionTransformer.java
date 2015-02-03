package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class InlineVersionTransformer extends BoogieTransformer {

	Collection<Declaration> mNonProcedureDeclarations;
	Map<String, CallGraphNode> mCallGraph;
	ScopedHashMap<String, String> mTypesMap = new ScopedHashMap<>();
	ScopedHashMap<String, String> mConstantsAndVariablesMap = new ScopedHashMap<>();
	ScopedHashMap<String, String> mLabelsMap = new ScopedHashMap<>();

	public InlineVersionTransformer(Map<String, CallGraphNode> callGraph,
			Collection<Declaration> nonProcedureDeclarations) {
		mNonProcedureDeclarations = nonProcedureDeclarations;
		mCallGraph = callGraph;
		initGlobalScopes();
	}
	
	private void initGlobalScopes() {
		for (Declaration decl : mNonProcedureDeclarations) {
			if (decl instanceof TypeDeclaration) {
				TypeDeclaration typeDecl = (TypeDeclaration) decl;
				typeDecl.getIdentifier();
			} else if (decl instanceof ConstDeclaration) {
				ConstDeclaration constDecl = (ConstDeclaration) decl;
				addGlobalVarsOrConsts(constDecl.getVarList());
			} else if (decl instanceof VariableDeclaration) {
				VariableDeclaration varDecl = (VariableDeclaration) decl;
				addGlobalVarsOrConsts(varDecl.getVariables());
			}
		}
	}
	
	private void addGlobalVarsOrConsts(VarList... varLists) {
		for (VarList varList : varLists) {			
			for (String id : varList.getIdentifiers()) {
				mConstantsAndVariablesMap.put(id, id);
			}
		}
	}

}
