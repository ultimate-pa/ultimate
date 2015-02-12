package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

public class InlineVersionTransformer extends BoogieTransformer {

	public static class GlobalScopeInitializer {
	
		private Map<VarMapKey, VarMapValue> mGlobalVars = new HashMap<>();

		public GlobalScopeInitializer(Collection<Declaration> nonProcedureDeclarations) {
			for (Declaration decl : nonProcedureDeclarations) {
				 if (decl instanceof ConstDeclaration) {
					ConstDeclaration constDecl = (ConstDeclaration) decl;
					addVarsOrConsts(constDecl.getVarList());
				} else if (decl instanceof VariableDeclaration) {
					VariableDeclaration varDecl = (VariableDeclaration) decl;
					addVarsOrConsts(varDecl.getVariables());
				}
			}			
		}
	
		private void addVarsOrConsts(VarList... varLists) {
			DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
			for (VarList varList : varLists) {			
				for (String id : varList.getIdentifiers()) {
					VarMapKey key = new VarMapKey(id, declInfo, false);
					VarMapValue value = new VarMapValue(id, declInfo);
					mGlobalVars.put(key, value);
				}
			}
		}
		
		/** @return New map from global variables and constants to the same values. */
		public Map<VarMapKey, VarMapValue> initVarMap() {
			return new HashMap<VarMapKey, VarMapValue>(mGlobalVars);
		}
		
		public void initVarIdManager(IdManager varIdManager) {
			for (VarMapKey globalVarKey : mGlobalVars.keySet()) {
				varIdManager.addId(globalVarKey.getVarId());
			}
		}
	}

	private IUltimateServiceProvider mServices;
	
	/**
	 * Similar to a call stack on execution, this contains the currently processed procedures.
	 * The entry procedure is on the bottom of the stack.
	 * Procedures of call-forall statements aren't pushed onto the stack. 
	 */
	private Deque<CallGraphNode> mProcedureStack = new ArrayDeque<>();
	
	/**
	 * Contains the number of (in the order of the program) processed calls
	 * inside the procedures of {@link #mProcedureStack}.
	 */
	private Deque<Integer> mEdgeIndexStack = new ArrayDeque<>();
	
	/**
	 * Counts for each procedure, how often it was called in the inlining process.
	 * The parameters and local variables of a Procedure are mapped, iff call counter > 0.
	 */
	private Map<String, Integer> mCallCounter = new HashMap<>();
	
	/** Determines, in how many nested "old(...)" expression the processing takes place. */
	private int mOldExprDepthCounter = 0;
	
	/** Variables which have to be added to the local variables of the entry point. */
	private List<VariableDeclaration> mInlinedVars = new ArrayList<>();
	
	/** Mapping from old variable identifiers to new ones. */
	private Map<VarMapKey, VarMapValue> mVarMap; // initialized by the GlobalScopeInitializer inside the ctor
	
	/** Manages the used variable identifiers. */
	private IdManager mVarIdManager = new IdManager();

	/** Mapping from the old label identifiers to new ones. */
	private Map<LabelMapKey, String> mLabelMap = new HashMap<>();
	
	/** Manages the used label identifiers. */
	private IdManager mLabelIdManager = new IdManager();
	
	public InlineVersionTransformer(IUltimateServiceProvider services, GlobalScopeInitializer globalScopeInit) {
		mServices = services;
		mVarMap = globalScopeInit.initVarMap();
		globalScopeInit.initVarIdManager(mVarIdManager);
	}

	public Procedure inlineCallsInside(CallGraphNode entryNode) throws CancelToolchainException {
		mProcedureStack.push(entryNode);
		mEdgeIndexStack.push(0);
		
		mapVariablesOfCurrentProcedure();
		Procedure proc = entryNode.getProcedureWithBody();
		Procedure newProc = null;
		if (entryNode.isImplemented()) {
			Body body = proc.getBody();
			List<VariableDeclaration> newLocalVars = new ArrayList<>();
			newLocalVars.addAll(Arrays.asList(body.getLocalVars()));
			newLocalVars.addAll(mInlinedVars);
			List<Statement> newBlock = new ArrayList<>();
			for (Statement stat : body.getBlock()) {
				newBlock.addAll(flattenStatement(stat));
			}
			VariableDeclaration[] newLocalVarsArray = new VariableDeclaration[newLocalVars.size()];
			newLocalVars.toArray(newLocalVarsArray);
			Statement[] newBlockArray = new Statement[newBlock.size()];
			newBlock.toArray(newBlockArray);
			Body newBody = new Body(body.getLocation(), newLocalVarsArray, newBlockArray);
			ModelUtils.mergeAnnotations(body, newBody);
			newProc = new Procedure(proc.getLocation(), proc.getAttributes(), proc.getIdentifier(),
					proc.getTypeParams(), proc.getInParams(), proc.getOutParams(), proc.getSpecification(), newBody);
			ModelUtils.mergeAnnotations(proc, newProc);
		}

		mProcedureStack.pop();
		mEdgeIndexStack.pop();

		return newProc;
	}

	/**
	 * Searches the procedure stack for duplicates.
	 * A duplicate inside the stack only occurs in case of recursion.
	 * @return The procedure stack contained a duplicate.
	 */
	private boolean stackContainsDuplicates() {
		Set<String> procIds = new HashSet<>();
		for (CallGraphNode node : mProcedureStack) {
			if(!procIds.add(node.getId())) {
				return true;
			}
		}
		return false;
	}

	/** @return The process takes places inside the entry procedure, according to the procedure stack. */
	private boolean inEntryProcedure() {
		return mProcedureStack.size() == 1;
	}
	
	private void mapVariablesOfCurrentProcedure() {
		CallGraphNode proc = mProcedureStack.peek();		
		Integer callCounter = mCallCounter.get(proc.getId());
		if (callCounter != null && callCounter > 0) {
			return;
		} else {
			Procedure procWithSpec = proc.getProcedureWithSpecification();
			Procedure procWithBody = proc.getProcedureWithBody();
			
			boolean isImplemented = proc.isImplemented();
			if (isImplemented && !proc.isCombined()) {
				mapProcedureParametersToSameValue(procWithSpec.getInParams(), procWithBody.getInParams(), true);
				mapProcedureParametersToSameValue(procWithSpec.getOutParams(), procWithBody.getOutParams(), false);
			} else {
				mapProcedureParameters(procWithSpec);
				if (isImplemented) {
					mapProcedureParameters(procWithBody);
				}
			}

			if (proc.isImplemented()) {
				Body body = procWithBody.getBody();
				for (VariableDeclaration localVarDecl : body.getLocalVars()) {
					mapLocalVariables(localVarDecl);
				}
			}			
		}
	}

	private void mapProcedureParametersToSameValue(VarList[] paramsProcDecl, VarList[] paramsProcImpl,
			boolean inParams) {
		boolean inEntryProc = inEntryProcedure();
		String originalProcId = mProcedureStack.peek().getId();
		String entryProcId = mProcedureStack.peekLast().getId();
		StorageClass storageClassProcDecl =
				inParams ? StorageClass.PROC_FUNC_INPARAM : StorageClass.PROC_FUNC_OUTPARAM;
		StorageClass storageClassProcImpl =
				inParams ? StorageClass.IMPLEMENTATION_INPARAM : StorageClass.IMPLEMENTATION_OUTPARAM;
		DeclarationInformation oldDeclInfoProcDecl = new DeclarationInformation(storageClassProcDecl, originalProcId);
		DeclarationInformation oldDeclInfoProcImpl = new DeclarationInformation(storageClassProcImpl, originalProcId);
		DeclarationInformation newDeclInfo = new DeclarationInformation(StorageClass.LOCAL, entryProcId);

		List<VariableDeclaration> inlinedVars = new ArrayList<>();
		final int gProcDecl = 0;
		final int gProcImpl = 1;
		// Only one identifier and location can be used for the new variable.
		final int gUsed = gProcImpl;
		final int gUnused = (gUsed+1) % 2;
		VarListIterator iterator = new VarListIterator(paramsProcDecl, paramsProcImpl);
		while (iterator.hasNext()) {
			iterator.next();
			
			// Map parameters of implementation and declaration to the same identifiers
			String usedParamId = iterator.currentId(gUsed);
			String newParamId;
			if (inEntryProc) {
				newParamId = usedParamId;
			} else {
				newParamId = mVarIdManager.makeAndAddUniqueId(originalProcId, usedParamId);				
			}
			VarMapKey keyProcDecl = new VarMapKey(iterator.currentId(gProcDecl), oldDeclInfoProcDecl, false);
			VarMapKey keyProcImpl = new VarMapKey(iterator.currentId(gProcImpl), oldDeclInfoProcImpl, false);
			VarMapValue value = new VarMapValue(newParamId, newDeclInfo);
			mVarMap.put(keyProcDecl, value);
			mVarMap.put(keyProcImpl, value);
			
			if (!inEntryProc) {
				// Create locale VariableDeclaration for inlining into entry procedure
				VarList usedVarList = iterator.currentVarList(gUsed);
				VarList unusedVarList = iterator.currentVarList(gUnused);
				ILocation location = usedVarList.getLocation();
				String[] identifiers = { newParamId };
				assert usedVarList.getType().getBoogieType().equals(unusedVarList.getType().getBoogieType());
				ASTType type = usedVarList.getType();
				Expression whereClause = usedVarList.getWhereClause();
				if (whereClause != null) {
					whereClause = processExpression(whereClause);
				}
				Attribute[] attrs = {};
				VarList variables = new VarList(location, identifiers, type, whereClause);
				ModelUtils.mergeAnnotations(usedVarList, variables);
				ModelUtils.mergeAnnotations(unusedVarList, variables);
				inlinedVars.add(new VariableDeclaration(location, attrs, new VarList[]{ variables }));				
			}
		}
		mInlinedVars.addAll(inlinedVars);
	}

	private void mapLocalVariables(VariableDeclaration varDecl) {
		List<VarList> inlinedVars = mapVariables(varDecl.getVariables(), StorageClass.LOCAL);
		if (!inEntryProcedure()) {
			Attribute[] newAttrs = processAttributes(varDecl.getAttributes());
			VarList[] newVarLists = new VarList[inlinedVars.size()];
			inlinedVars.toArray(newVarLists);
			VariableDeclaration newVarDecl = new VariableDeclaration(varDecl.getLocation(), newAttrs, newVarLists);
			ModelUtils.mergeAnnotations(varDecl, newVarDecl);
			mInlinedVars.add(newVarDecl);
		}
	}

	private void mapProcedureParameters(Procedure proc) {
		boolean hasSpec = proc.getSpecification() != null;
		List<VarList> inlinedVars = new ArrayList<>(proc.getInParams().length + proc.getOutParams().length);
		inlinedVars.addAll(mapVariables(proc.getInParams(),
				hasSpec ? StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM));
		inlinedVars.addAll(mapVariables(proc.getOutParams(),
				hasSpec ? StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM));
		if (!inEntryProcedure()) {
			Attribute[] newAttrs = {};
			VarList[] newVarLists = new VarList[inlinedVars.size()];
			inlinedVars.toArray(newVarLists);
			VariableDeclaration newVarDecl = new VariableDeclaration(proc.getLocation(), newAttrs, newVarLists);
			mInlinedVars.add(newVarDecl);
		}
	}
	
	private void mapQuantifierParameters(QuantifierExpression quantifierExpr) {
		mapVariables(quantifierExpr.getParameters(), StorageClass.QUANTIFIED);
		// quantified vars don't have to be added to the inlined local variables
	}

	private void mapVariableInOldExpr(IdentifierExpression idExpr) {
		/* TODO implement
		VarMapKey key = new VarMapKey(idExpr.getIdentifier(), idExpr.getDeclarationInformation(), true);
		if (mVariablesMap.containsKey(key)) {
			return;
		}
		
		VarMapValue value = null;
		if (idExpr.getDeclarationInformation().getStorageClass() == StorageClass.GLOBAL) {
			DeclarationInformation newDeclInfo = new DeclarationInformation(StorageClass.LOCAL);
			value = new VarMapValue(varId, newDeclInfo);
			
		} else {
			VarMapKey nonOldKey = new VarMapKey(idExpr.getIdentifier(), idExpr.getDeclarationInformation(), false);
			value = mVariablesMap.get(nonOldKey);
		}
		*/
	}
	
	/**
	 * Generates new unique identifiers for variables and updates the map.
	 * This method is only for VarLists that are part of a procedure (no global variables for instance).
	 * @param varLists Variables to be processed (must be part of a procedure).
	 * @param storageClass StorageClass of the variables.
	 * @return List of VarLists, with new names and the same types.
	 * 		   Use this to inline the processed variables as local variables.
	 */
	private List<VarList> mapVariables(VarList[] varLists, StorageClass storageClass) {
		String originalProcId = mProcedureStack.peek().getId();
		String entryProcId = mProcedureStack.peekLast().getId();
		boolean isQuantified = storageClass == StorageClass.QUANTIFIED;
		DeclarationInformation oldDeclInfo = new DeclarationInformation(storageClass,
				isQuantified ? null : originalProcId);
		DeclarationInformation newDeclInfo = new DeclarationInformation(storageClass,
				isQuantified ? null : entryProcId);
		List<VarList> newVarLists = new ArrayList<>();
		for (VarList varList : varLists) {
			List<String> newVarIds = new ArrayList<>();
			for (String varId : varList.getIdentifiers()) {
				String newVarId;
				if (inEntryProcedure()) {
					newVarId = mVarIdManager.addId(varId);
				} else {
					// DeclarationInformations of quantified vars contain no procedure, hence the prefix doesn't too.
					String prefix = isQuantified ? "quantified" : originalProcId;
					newVarId = mVarIdManager.makeAndAddUniqueId(prefix, varId);
					newVarIds.add(newVarId);
				}
				VarMapKey key = new VarMapKey(varId, oldDeclInfo, false);
				VarMapValue value = new VarMapValue(newVarId, newDeclInfo);
				// quantified vars with the same id could be already mapped -- don't change the mapping for them!
				if (!mVarMap.containsKey(key)) {
					mVarMap.put(key, value);					
				} else {
					assert isQuantified;
				}
			}
			String[] newVarIdsArray = new String[newVarIds.size()];
			newVarIds.toArray(newVarIdsArray);
			Expression whereClause = varList.getWhereClause();
			Expression newWhereClause = whereClause != null ? processExpression(whereClause) : null;
			VarList newVarList = new VarList(varList.getLocation(), newVarIdsArray, varList.getType(), newWhereClause);
			ModelUtils.mergeAnnotations(varList, newVarList);
			newVarLists.add(newVarList);
		}
		return newVarLists;
	}
	
	
	
	private List<Statement> flattenStatement(Statement stat) {
		/* TODO implement inlineCall(...)
		if (stat instanceof CallStatement) {
			// TODO increment call counter
			CallStatement call = (CallStatement) stat;
			int edgeIndex = mCallGraphEdgeStack.pop();
			mCallGraphEdgeStack.push(edgeIndex + 1);
			CallGraphNode node = mProcedureStack.peek();
			CallGraphEdgeLabel edgeLabel = node.getOutgoingEdgeLabels().get(edgeIndex);
			if (edgeLabel.getInlineFlag()) {
				return inlineCall(call);
			}
		}
		*/
		return Collections.singletonList(processStatement(stat));
	}
	
	private List<Statement> inlineCall(CallStatement call) {
		// TODO implement
		return null;
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
			LabelMapKey key = new LabelMapKey(labelName, mProcedureStack.peek().getId());
			mLabelMap.put(key, labelName);
		}
	}
	
	@Override
	protected Expression processExpression(Expression expr) {
		/* TODO finish implementation
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression idExpr = (IdentifierExpression) expr;
			boolean inOldExpr = mOldExprDepthCounter > 0 && !inEntryProcedure();
			if (inOldExpr) {
				mapVariableInOldExpr(idExpr);				
			}
			VarMapValue mapValue = mVariablesMap.get(new VarMapKey(
					idExpr.getIdentifier(), idExpr.getDeclarationInformation(), inOldExpr));
			IdentifierExpression newIdExpr = new IdentifierExpression(
					idExpr.getLocation(), idExpr.getType(), mapValue.getVarId(), mapValue.getDeclInfo());
			return null;
		} else if (expr instanceof UnaryExpression && ((UnaryExpression) expr).getOperator() == Operator.OLD) {
			UnaryExpression unaryExpr = (UnaryExpression) expr;
			++mOldExprDepthCounter;
			Expression newExpr = processExpression(unaryExpr.getExpr());
			--mOldExprDepthCounter;
			ModelUtils.mergeAnnotations(expr, newExpr);
			return newExpr;
		} else {
			return super.processExpression(expr);
		}
		*/
		return super.processExpression(expr);
	}

}
