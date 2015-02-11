package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class InlineVersionTransformer extends BoogieTransformer {

	public static class GlobalScopeInitializer {
	
		private Map<VarMapKey, VarMapValue> mVariablesMap = new HashMap<>();
		private Set<String> mGlobalTypes = new HashSet<>();
		
		public GlobalScopeInitializer(Collection<Declaration> nonProcedureDeclarations) {
			addPredefinedTypes();
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

		private void addPredefinedTypes() {
			mGlobalTypes.add("bool");
			mGlobalTypes.add("int");
		}
		
		private void addTypes(TypeDeclaration typeDecl) {
			mGlobalTypes.add(typeDecl.getIdentifier());
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

		@Override
		public String toString() {
			return "GlobalScopeInitializer [mVariablesMap=" + mVariablesMap + ", mGlobalTypes=" + mGlobalTypes + "]";
		}
		
		public Map<VarMapKey, VarMapValue> createVarMap() {
			return new HashMap<VarMapKey, VarMapValue>(mVariablesMap);
		}
		
		public ScopedHashMap<String, String> createTypeMap() {
			ScopedHashMap<String, String> typesMap = new ScopedHashMap<>();
			for (String type : mGlobalTypes) {
				typesMap.put(type, type);
			}
			return typesMap;
		}
	}

	IUltimateServiceProvider mServices;
	
	Map<VarMapKey, VarMapValue> mVariablesMap;
	Map<LabelMapKey, String> mLabelsMap;
	ScopedHashMap<String, String> mTypesMap;

	CallGraphNode mCurrentNode;

	Collection<VariableDeclaration> inlinedVariables = new ArrayList<VariableDeclaration>();

	
	public InlineVersionTransformer(IUltimateServiceProvider services, GlobalScopeInitializer globalScopeInit) {
		mServices = services;
		mVariablesMap = globalScopeInit.createVarMap();
		mLabelsMap = new HashMap<LabelMapKey, String>();
		mTypesMap = globalScopeInit.createTypeMap();
	}
	
	public Procedure process(CallGraphNode entryNode) {
		mCurrentNode = entryNode;
		Procedure procWithBody = entryNode.getProcedureWithBody();
		if (hasCallsWithInlineFlags(entryNode)) {
			registerEntryPoint();
			Procedure newProcWithBody = /* TODO process */ procWithBody;
			return newProcWithBody;
		} else {
			return procWithBody;
		}
	}

	private boolean hasCallsWithInlineFlags(CallGraphNode node) {
		for (CallGraphEdgeLabel outgoingLabel : node.getOutgoingEdgeLabels()) {
			if (outgoingLabel.getInlineFlag()) {
				return true;
			}
		}
		return false;
	}
	
	private void registerEntryPoint() {
		Procedure proc = mCurrentNode.getProcedureWithBody();
		for (String typeArg : proc.getTypeParams()) {
			mTypesMap.put(typeArg, typeArg);
		}
		boolean combinedProcDeclAndImpl = proc.getSpecification() != null;
		registerVariables(proc.getInParams(),
				combinedProcDeclAndImpl ? StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM);
		registerVariables(proc.getOutParams(),
				combinedProcDeclAndImpl ? StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM);
		Body body = proc.getBody();
		for (VariableDeclaration localVarDecl : body.getLocalVars()) {
			registerVariables(localVarDecl.getVariables(), StorageClass.LOCAL);
		}
		registerLabels(body.getBlock());
	}
	
	private void registerVariables(VarList[] varLists, StorageClass storageClass) {
		DeclarationInformation declInfo = new DeclarationInformation(storageClass, mCurrentNode.getId());
		for (VarList varList : varLists) {
			IType type = varList.getType().getBoogieType();
			for (String varId : varList.getIdentifiers()) {
				VarMapKey key = new VarMapKey(varId, declInfo, type);
				VarMapValue value = new VarMapValue(varId, type);
				mVariablesMap.put(key, value);
			}
		}
	}
	
	private void registerLabels(Statement[] stats) {
		for (Statement stat : stats) {
			registerLabels(stat);
		}
	}
	
	private void registerLabels(Statement stat) {
		if (stat instanceof WhileStatement) {
			registerLabels(((WhileStatement) stat).getBody());
		} else if (stat instanceof IfStatement) {
			IfStatement ifStat = (IfStatement) stat;
			registerLabels(ifStat.getThenPart());
			registerLabels(ifStat.getElsePart());
		} else if (stat instanceof Label) {
			String labelName = ((Label) stat).getName();
			LabelMapKey key = new LabelMapKey(labelName, mCurrentNode.getId());
			mLabelsMap.put(key, labelName);
		}
	}
	
	@Override
	protected Procedure processDeclaration(Declaration decl) {
		assert decl instanceof Procedure;
		Procedure proc = (Procedure) decl;
		Procedure newProc = null;
		Attribute[] attrs = proc.getAttributes();
		Attribute[] newAttrs = processAttributes(attrs);
		
		// TODO implement
		
		return newProc;
	}

}
