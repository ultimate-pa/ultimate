package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
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
	private Deque<Integer> mCallGraphEdgeStack = new ArrayDeque<>();
	
	/** Counts for each procedure, how often it was called in the inlining process. */
	private Map<String, Integer> mCallCounter = new HashMap<>();
	
	/** Determines, in how many nested "old(...)" expression the processing takes place. */
	private int mOldExprDepthCounter = 0;
	
	/** Variables which have to be added to the local variables of the entry point. */
	private List<VariableDeclaration> mInlinedVariables = new ArrayList<>();
	
	/** Mapping from old variable identifiers to new ones. */
	private Map<VarMapKey, VarMapValue> mVariablesMap; // initialized by the GlobalScopeInitializer inside the ctor
	
	/** Manages the used variable identifiers. */
	private IdManager mVariablesIdManager = new IdManager();

	/** Mapping from the old label identifiers to new ones. */
	private Map<LabelMapKey, String> mLabelsMap = new HashMap<>();
	
	/** Manages the used label identifiers. */
	private IdManager mLabelsIdManager = new IdManager();
	
	public InlineVersionTransformer(IUltimateServiceProvider services, GlobalScopeInitializer globalScopeInit) {
		mServices = services;
		mVariablesMap = globalScopeInit.initVarMap();
	}

	public Procedure inlineCallsInside(CallGraphNode entryNode) throws CancelToolchainException {
		mProcedureStack.push(entryNode);
		mCallGraphEdgeStack.push(0);
		
		mapVariablesOfCurrentProcedure();
		Procedure proc = entryNode.getProcedureWithBody();
		Procedure newProc = null;
		if (entryNode.isImplemented()) {
			Body body = proc.getBody();
			List<VariableDeclaration> newLocalVars = new ArrayList<>();
			newLocalVars.addAll(Arrays.asList(body.getLocalVars()));
			newLocalVars.addAll(mInlinedVariables);
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
		mCallGraphEdgeStack.pop();

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
		
		// TODO map parameters of procedure and implementation to the same identifiers (this is vital!)

		CallGraphNode proc = mProcedureStack.peek();
		Procedure procWithSpec = proc.getProcedureWithSpecification();
		Procedure procWithBody = proc.getProcedureWithBody();
		mapProcedureParameters(procWithSpec);
		if (proc.isImplemented()) {
			if (!proc.isCombined()) {
				mapProcedureParameters(procWithBody);
			}
			Body body = procWithBody.getBody();
			for (VariableDeclaration localVarDecl : body.getLocalVars()) {
				mapLocalVariables(localVarDecl);
			}
		}
	}
	
	private void mapLocalVariables(VariableDeclaration varDecl) {
		List<VarList> inlinedVars = mapVariables(varDecl.getVariables(), StorageClass.LOCAL);
		if (!inEntryProcedure()) {
			Attribute[] newAttrs = processAttributes(varDecl.getAttributes());
			VarList[] newVarLists = new VarList[inlinedVars.size()];
			inlinedVars.toArray(newVarLists);
			VariableDeclaration newVarDecl = new VariableDeclaration(varDecl.getLocation(), newAttrs, newVarLists);
			ModelUtils.mergeAnnotations(varDecl, newVarDecl);
			mInlinedVariables.add(newVarDecl);
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
			mInlinedVariables.add(newVarDecl);
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
					newVarId = mVariablesIdManager.addId(varId);
				} else {
					// DeclarationInformations of quantified vars contain no procedure, hence the prefix doesn't too.
					String prefix = isQuantified ? "quantified" : originalProcId;
					newVarId = mVariablesIdManager.makeAndAddUniqueId(prefix, varId);
					newVarIds.add(newVarId);
				}
				VarMapKey key = new VarMapKey(varId, oldDeclInfo, false);
				VarMapValue value = new VarMapValue(newVarId, newDeclInfo);
				// quantified vars with the same id could be already mapped -- don't change the mapping for them!
				if (!mVariablesMap.containsKey(key)) {
					mVariablesMap.put(key, value);					
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
			mLabelsMap.put(key, labelName);
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
