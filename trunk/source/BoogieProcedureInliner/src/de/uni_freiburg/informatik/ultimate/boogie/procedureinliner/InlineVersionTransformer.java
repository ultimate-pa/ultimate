package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;

public class InlineVersionTransformer extends BoogieTransformer {

	public static class GlobalScopeInitializer {
	
		private Map<VarMapKey, VarMapValue> mVariablesMap = new HashMap<>();
		private Map<String, String> mTypesMap = new HashMap<>();
		
		public GlobalScopeInitializer(Collection<Declaration> nonProcedureDeclarations) {
			for (Declaration decl : nonProcedureDeclarations) {
				if (decl instanceof TypeDeclaration) {
					TypeDeclaration typeDecl = (TypeDeclaration) decl;
					addTypes(typeDecl);
				} else if (decl instanceof ConstDeclaration) {
					ConstDeclaration constDecl = (ConstDeclaration) decl;
					addVarsOrConsts(constDecl.getVarList());
				} else if (decl instanceof VariableDeclaration) {
					VariableDeclaration varDecl = (VariableDeclaration) decl;
					addVarsOrConsts(varDecl.getVariables());
				}
			}			
		}
		
		private void addVarsOrConsts(VarList... varLists) {
			for (VarList varList : varLists) {			
				for (String id : varList.getIdentifiers()) {
					IType type = varList.getType().getBoogieType();
					VarMapKey key = new VarMapKey(id, new DeclarationInformation(StorageClass.GLOBAL, null), type);
					VarMapValue value = new VarMapValue(id, type);
					mVariablesMap.put(key, value);
				}
			}
		}
		
		private void addTypes(TypeDeclaration typeDecl) {
			String id = typeDecl.getIdentifier();
			mTypesMap.put(id, id);
		}

		@Override
		public String toString() {
			return "GlobalScopeInitializer [mVariablesMap=" + mVariablesMap + ", mTypesMap=" + mTypesMap + "]";
		}
	}

	IUltimateServiceProvider mServices;
	
	Map<VarMapKey, VarMapValue> mVariablesMap;
	Map<LabelMapKey, String> mLabelsMap;
	Map<String, String> mTypesMap;

	Collection<VariableDeclaration> inlinedVariables = new ArrayList<VariableDeclaration>();
	
	public InlineVersionTransformer(IUltimateServiceProvider services, GlobalScopeInitializer globalScopeInit) {
		mServices = services;
		mVariablesMap = new HashMap<VarMapKey, VarMapValue>(globalScopeInit.mVariablesMap);
		mLabelsMap = new HashMap<LabelMapKey, String>();
		mTypesMap = new HashMap<String, String>(globalScopeInit.mTypesMap);
	}
	
	public Procedure process(CallGraphNode node) {
		// TODO: implement
		return node.getProcedureWithBody();
	}

}
