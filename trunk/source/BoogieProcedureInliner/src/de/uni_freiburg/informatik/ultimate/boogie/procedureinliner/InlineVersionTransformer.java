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

import javax.swing.text.html.HTMLDocument.HTMLReader.BlockAction;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences.PreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

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
	 * Contains the number of processed calls (in the order of the program)
	 * inside the procedures of {@link #mProcedureStack}.
	 */
	private Deque<Integer> mEdgeIndexStack = new ArrayDeque<>();
	
	/**
	 * Counts for each procedure, how much calls to this procedure where inlined (!) during the process.
	 * "call forall" statements count too. Non-inlined calls don't count!
	 * The parameters and local variables of a Procedure are mapped, iff call counter > 0.
	 * Note: This has nothing to do with the "single calls only" setting ({@link PreferenceItem#IGNORE_MULTIPLE_CALLED}.
	 * This counter is used to avoid re-mapping of already mapped variable ids, whereas the setting is applied using a
	 * separate counter on the call graph.
	 */
	private Map<String, Integer> mCallCounter = new HashMap<>();
	
	/** Contains the (possibly nested) "old(...)" expression(s), in which the processing takes place. */
	private ArrayDeque<UnaryExpression> mOldExprStack = new ArrayDeque<>();
	
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
	
	/** Assume the inlined "requires" specifications (preconditions) after they were asserted. */
	private boolean mAssumeRequiresAfterAssert;

	/** Assert the inlined "ensures" specifications (postconditions) before they are assumed. */
	private boolean mAssertEnsuresBeforeAssume;
	
	public InlineVersionTransformer(IUltimateServiceProvider services, GlobalScopeInitializer globalScopeInit,
			boolean assumeRequiresAfterAssert, boolean assertEnsuresBeforeAssume) {
		mServices = services;
		mVarMap = globalScopeInit.initVarMap();
		globalScopeInit.initVarIdManager(mVarIdManager);
		mAssumeRequiresAfterAssert = assumeRequiresAfterAssert;
		mAssertEnsuresBeforeAssume = assertEnsuresBeforeAssume;
	}

	/**
	 * Creates an equivalent Procedure with inlined calls.
	 * Only marked calls will be inlined (see {@link CallGraphEdgeLabel#setInlineFlag(boolean)}.
	 * 
	 * The returned Procedure has an Specification, iff the original Procedure was combined.
	 * 
	 * @param entryNode Call graph node, representing the procedure to be flattened.
	 * @return Equivalent procedure with inlined calls. {@code null} for unimplemented procedures.
	 * @throws CancelToolchainException If an error occurred and the toolchain should be canceled.
	 */
	public Procedure inlineCallsInside(CallGraphNode entryNode) throws CancelToolchainException {
		mProcedureStack.push(entryNode);
		mEdgeIndexStack.push(0);
		
		mapVariablesOfCurrentProcedure();
		Procedure newProc = null;
		if (entryNode.isImplemented()) {
			Procedure proc = entryNode.getProcedureWithBody();
			Body body = proc.getBody();
			Statement[] block = body.getBlock();
			List<Statement> newBlock = new ArrayList<>();
			mapLabels(block);
			for (Statement stat : block) {
				newBlock.addAll(flattenStatement(stat));
			}
			List<VariableDeclaration> newLocalVars = new ArrayList<>(mInlinedVars);
			VariableDeclaration[] newLocalVarsArray =
					newLocalVars.toArray(new VariableDeclaration[newLocalVars.size()]);
			Statement[] newBlockArray = newBlock.toArray(new Statement[newBlock.size()]);
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

	/**
	 * Get the number of inlined calls to a procedure.
	 * @param procId Identifier of the called procedure.
	 * @return Number of inlined calls to the procedure.
	 * @see #mCallCounter
	 */
	private int getCallCounter(String procId) {
		Integer callCounter = mCallCounter.get(procId);
		return callCounter == null ? 0 : callCounter;		
	}
	
	/**
	 * Increments the call counter for a given procedure.
	 * Use this method, when a call is inlined.
	 * @param procId Identifier of the procedure.
	 * @return Old call counter value of the procedure.
	 * @see #mCallCounter
	 */
	private int incrementCallCounter(String procId) {
		int oldValue = getCallCounter(procId);
		mCallCounter.put(procId, oldValue + 1);
		return oldValue;
	}

	/**
	 * Increments the edge index on top of the {@link #mEdgeIndexStack}.
	 * @return The edge index from the top of the stack, before it was incremented.
	 */
	private int getAndUpdateEdgeIndex() {
		int edgeIndex = mEdgeIndexStack.pop();
		mEdgeIndexStack.push(edgeIndex + 1);
		return edgeIndex;
	}

	/** Map input parameters, output parameters and local variables of the current procedure. */
	private void mapVariablesOfCurrentProcedure() {
		CallGraphNode proc = mProcedureStack.peek();
		Procedure procWithSpec = proc.getProcedureWithSpecification();
		Procedure procWithBody = proc.getProcedureWithBody();		
		if (proc.isImplemented()) {
			if (proc.isCombined()) {
				mapProcedureParameters(procWithBody);				
			} else {
				mapProcedureParametersToSameValue(procWithSpec.getInParams(), procWithBody.getInParams(), true);
				mapProcedureParametersToSameValue(procWithSpec.getOutParams(), procWithBody.getOutParams(), false);					
			}
			Body body = procWithBody.getBody();
			for (VariableDeclaration localVarDecl : body.getLocalVars()) {
				mapLocalVariables(localVarDecl);
			}
		} else {
			mapProcedureParameters(procWithSpec);
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
			Attribute[] newAttrs = {}; // Parameters can't have Attributes
			VarList[] newVarLists = new VarList[inlinedVars.size()];
			inlinedVars.toArray(newVarLists);
			VariableDeclaration newVarDecl = new VariableDeclaration(proc.getLocation(), newAttrs, newVarLists);
			mInlinedVars.add(newVarDecl);
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
		// indices
		final int gProcDecl = 0;
		final int gProcImpl = 1;
		final int gUsed = gProcImpl; // only one identifier and location can be used for the new variable
		final int gUnused = (gUsed+1) % 2; // the remaining index 
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
				// Create local VariableDeclaration for inlining into entry procedure
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
		if (stat instanceof CallStatement) {
			CallStatement call = (CallStatement) stat;
			int edgeIndex = getAndUpdateEdgeIndex();
			CallGraphNode callerNode = mProcedureStack.peek();
			CallGraphNode calleeNode = callerNode.getOutgoingNodes().get(edgeIndex);
			CallGraphEdgeLabel edgeLabel = callerNode.getOutgoingEdgeLabels().get(edgeIndex);
			assert call.getMethodName().equals(calleeNode.getId())
				&& call.getMethodName().equals(edgeLabel.getCalleeProcedureId());		
			if (edgeLabel.getInlineFlag()) {
				if (incrementCallCounter(calleeNode.getId()) <= 0) {
					mapVariablesOfCurrentProcedure();
				}
				if (call.isForall()) {
					return inlineCallForall(call, calleeNode);
				} else {
					return inlineCall(call, calleeNode);
				}
			}
		}
		return Collections.singletonList(processStatement(stat));
	}
	
	private List<Statement> inlineCallForall(CallStatement call, CallGraphNode calleeNode) {
		throw new UnsupportedOperationException("Call forall isn't supported yet."); // TODO support
	}

	private List<Statement> inlineCall(CallStatement call, CallGraphNode calleeNode) {
		mProcedureStack.push(calleeNode);
		final int currentCallCount = getCallCounter(calleeNode.getId());
		
		// inline specifications ---------
		Specification[] specs = calleeNode.getProcedureWithSpecification().getSpecification();
		List<Statement> assertRequires = new ArrayList<>();
		List<Statement> assumeRequires = new ArrayList<>();
		List<Statement> assertEnsures = new ArrayList<>();
		List<Statement> assumeEnsures = new ArrayList<>();
		for (Specification spec : processSpecifications(specs)) {
			ILocation loc = spec.getLocation();
			if (spec instanceof RequiresSpecification) {
				Expression formula = ((RequiresSpecification) spec).getFormula();
				assertRequires.add(new AssertStatement(loc, formula));	
				if (mAssumeRequiresAfterAssert) {
					assumeRequires.add(new AssumeStatement(loc, formula));
				}
			} else if (spec instanceof EnsuresSpecification) {
				Expression formula = ((EnsuresSpecification) spec).getFormula();
				if (mAssertEnsuresBeforeAssume) {
					// TODO don't assert when callee not implemented?
					assertEnsures.add(new AssertStatement(loc, formula));
				}
				assumeEnsures.add(new AssumeStatement(loc, formula));
			}
			// TODO merge Annotations (?)
		}

		// inline body ---------
		List<Statement> inlinedBody;
		if (calleeNode.isImplemented()) {
			Procedure procWithBody = calleeNode.getProcedureWithBody();
			Body body = procWithBody.getBody();
			Statement[] block = body.getBlock();
			mapLabels(block);
			mapReturnLabel();
			
			// TODO continue work here ---------------------------------------------------------------------------------
			// ...
			
			Label returnLabel = new Label(procWithBody.getLocation(), getCurrentReturnLabelId());
			// TODO add returnLabel to Body block (before assert/assume POST)
		} else {
			// TODO havoc (mind the where clauses!)
		}
		
		mProcedureStack.pop();
		return null; // TODO change
	}

	@Override
	protected Statement processStatement(Statement statement) {
		Statement newStatement = null;
		if (statement instanceof Label) {
			Label label = (Label) statement;
			newStatement = new Label(label.getLocation(), getNewLabelId(label.getName()));
		} else if (statement instanceof GotoStatement) {
			GotoStatement gotoStat = (GotoStatement) statement;
			String[] labelIds = gotoStat.getLabels();
			String[] newLabelIds = new String[labelIds.length];
			for (int i = 0; i < labelIds.length; ++i) {
				newLabelIds[i] = getNewLabelId(labelIds[i]);
			}
			newStatement = new GotoStatement(gotoStat.getLocation(), newLabelIds);
		} else if (statement instanceof BreakStatement) {
			BreakStatement breakStat = (BreakStatement) statement;
			String label = breakStat.getLabel();	
			newStatement = new BreakStatement(breakStat.getLocation(), label == null ? null : getNewLabelId(label));
		} else if (statement instanceof ReturnStatement && !inEntryProcedure()) {
			newStatement = new GotoStatement(statement.getLocation(), new String[] { getCurrentReturnLabelId() });
		}
		if (newStatement == null) {
			return super.processStatement(statement);			
		} else {
			ModelUtils.mergeAnnotations(statement, newStatement);
			return newStatement;
		}
	}

	private String getNewLabelId(String oldLabelId) {
		String newName = mLabelMap.get(oldLabelId);
		assert newName != null : "Missing mapping for Label: " + oldLabelId;
		return newName;
	}

	private void mapReturnLabel() {
		String procId = mProcedureStack.peek().getId();
		String returnLabelId = mLabelIdManager.makeAndAddUniqueId(procId, "returnLabel");
		mLabelMap.put(createCurrentReturnLabelKey() , returnLabelId);
	}
	
	private String getCurrentReturnLabelId() {
		return mLabelMap.get(createCurrentReturnLabelKey());
	}
	
	private LabelMapKey createCurrentReturnLabelKey() {
		String procId = mProcedureStack.peek().getId();
		return new LabelMapKey(null, procId, getCallCounter(procId));
	}
	
	private void mapLabels(Statement[] stats) {
		for (Statement stat : stats) {
			mapLabels(stat);
		}
	}
	
	private void mapLabels(Statement stat) {
		if (stat instanceof WhileStatement) {
			mapLabels(((WhileStatement) stat).getBody());
		} else if (stat instanceof IfStatement) {
			IfStatement ifStat = (IfStatement) stat;
			mapLabels(ifStat.getThenPart());
			mapLabels(ifStat.getElsePart());
		} else if (stat instanceof Label) {
			String procId = mProcedureStack.peek().getId();
			String labelId = ((Label) stat).getName();
			String newLabelId;
			if (inEntryProcedure()) {
				newLabelId = mLabelIdManager.addId(procId);
			} else {
				newLabelId = mLabelIdManager.makeAndAddUniqueId(procId, labelId);				
			}
			LabelMapKey key = new LabelMapKey(labelId, procId, getCallCounter(procId));
			mLabelMap.put(key, newLabelId);
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
