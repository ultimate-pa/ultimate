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
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences.PreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class InlineVersionTransformer extends BoogieTransformer {

	public static class GlobalScopeManager {

		private Map<VarMapKey, VarMapValue> mVarMap = new HashMap<>();
		
		/**
		 * Maps identifiers from global constants or variables to their Declarations.
		 * The values are either ConstDeclarations or VariableDeclarations.
		 */
		private Map<String, Declaration> mVarDecls = new HashMap<>();
		
		/** Maps identifiers from global constants or variables to the VarLists from their Declarations. */
		private Map<String, VarList> mVarLists = new HashMap<>();
		
		public GlobalScopeManager(Collection<Declaration> nonProcedureDeclarations) {
			for (Declaration decl : nonProcedureDeclarations) {
				 if (decl instanceof ConstDeclaration) {
					ConstDeclaration constDecl = (ConstDeclaration) decl;
					VarList varList = constDecl.getVarList();
					addVarsOrConsts(varList);
					for (String id : varList.getIdentifiers()) {
						mVarDecls.put(id, constDecl);
						mVarLists.put(id, varList);
					}
				} else if (decl instanceof VariableDeclaration) {
					VariableDeclaration varDecl = (VariableDeclaration) decl;
					for (VarList varList : varDecl.getVariables()) {
						addVarsOrConsts(varList);
						for (String id : varList.getIdentifiers()) {
							mVarDecls.put(id, varDecl);
							mVarLists.put(id, varList);
						}
					}
				}
			}	
		}

		private void addVarsOrConsts(VarList varList) {
			List<String> ids = new ArrayList<>();
			DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
			for (String id : varList.getIdentifiers()) {
				VarMapKey key = new VarMapKey(id, declInfo);
				VarMapValue value = new VarMapValue(id, declInfo);
				mVarMap.put(key, value);
				ids.add(id);
			}
		}
		
		/** @return New map from global variables and constants to the same values. */
		public Map<VarMapKey, VarMapValue> initVarMap() {
			return new HashMap<VarMapKey, VarMapValue>(mVarMap);
		}
		
		public void initVarIdManager(IdManager varIdManager) {
			for (VarMapKey globalVarKey : mVarMap.keySet()) {
				varIdManager.addId(globalVarKey.getVarId());
			}
		}
		
		/**
		 * Gets the Declaration, containing a given global variable or constant.
		 * @param id Identifier of the global variable or constant.
		 * @return Declaration or null, if no global variable or constant had the given id.
		 *         The Declaration is either of type VariableDeclaration or ConstDeclaration.
		 */
		public Declaration getVarDeclaration(String id) {
			return mVarDecls.get(id);
		}

		/**
		 * Gets the VarList from a VariableDeclaration or ConstDeclaration,
		 * containing a given global variable or constant.
		 * @param id Identifier of the global variable or constant.
		 * @return VarList or null, if no global variable or constant had the given id.
		 */
		public VarList getVarListFromDeclaration(String id) {
			return mVarLists.get(id);
		}
	}

	private IUltimateServiceProvider mServices;

	private GlobalScopeManager mGlobalScopeManager;
	
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
	
	/**
	 * Contains the (possibly nested) "old(...)" expression(s), in which the processing takes place.
	 * Only old() expressions that are inlined (in other words: removed) are stored.
	 * This stack is based on Expressions.
	 */
	private Deque<UnaryExpression> mInlinedOldExprStack = new ArrayDeque<>();
	
	/**
	 * Keeps track of global variables, which appeared inside inlined old() expressions.
	 * Nested inlined procedures need their own old-variables. The top of the stack contains the variables for the
	 * currently processed procedure.
	 * The stored VariablesLHS are the unmodified global variables.
	 * 
	 * This stack is based on Procedures.
	 */
	private Deque<List<VariableLHS>> mInlinedOldVarStack = new ArrayDeque<>();
	
	/** Variables which have to be added to the local variables of the entry point. */
	private List<VariableDeclaration> mInlinedVars = new ArrayList<>();
	
	/** Mapping from original variable identifiers to new ones. */
	private Map<VarMapKey, VarMapValue> mVarMap;
	
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
	
	/**
	 * Creates a new InlineVersionTransformer.
	 * @param services Services
	 * @param globalScopeManager GlobalScopeManager, has to be initialized already
	 * @param assumeRequiresAfterAssert Assume inlined preconditions after they were asserted.
	 * @param assertEnsuresBeforeAssume Assert inlined postconditions before they are assumed.
	 *                                  This setting only applies to implemented procedures.
	 */
	public InlineVersionTransformer(IUltimateServiceProvider services, GlobalScopeManager globalScopeManager,
			boolean assumeRequiresAfterAssert, boolean assertEnsuresBeforeAssume) {
		mServices = services;
		mGlobalScopeManager = globalScopeManager;
		mVarMap = globalScopeManager.initVarMap();
		globalScopeManager.initVarIdManager(mVarIdManager);
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
			String procId = proc.getIdentifier();
			Body body = proc.getBody();
			Statement[] block = body.getBlock();
			mapLabels(block);
			Statement[] newBlock = flattenStatementsArray(block);

			List<VariableDeclaration> newLocalVars = new ArrayList<>();
			DeclarationInformation localDeclInfo = new DeclarationInformation(StorageClass.LOCAL, procId);
			for (VariableDeclaration localVarDecl : body.getLocalVars()) {
				Attribute[] attrs = localVarDecl.getAttributes();
				Attribute[] newAttrs = processAttributes(attrs);
				VarList[] vars = localVarDecl.getVariables();
				VarList[] newVars = applyMappingToVarList(vars, localDeclInfo);
				VariableDeclaration newLocalVarDecl;
				if (newAttrs != attrs || newVars != vars) {
					newLocalVarDecl = new VariableDeclaration(localVarDecl.getLocation(), newAttrs, newVars);
					ModelUtils.mergeAnnotations(localVarDecl, newLocalVarDecl);
				} else {
					newLocalVarDecl = localVarDecl;
				}
				newLocalVars.add(newLocalVarDecl);
			}
			newLocalVars.addAll(mInlinedVars);

			Body newBody = new Body(body.getLocation(),
					newLocalVars.toArray(new VariableDeclaration[newLocalVars.size()]), newBlock);
			ModelUtils.mergeAnnotations(body, newBody);
			
			Specification[] oldSpecs = proc.getSpecification();
			boolean hasSpec = oldSpecs != null;
			Specification[] newSpecs = hasSpec ? processSpecifications(oldSpecs) : null;	
			
			VarList[] newInParams = applyMappingToVarList(proc.getInParams(), new DeclarationInformation(
					hasSpec ? StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM, procId));
			VarList[] newOutParams = applyMappingToVarList(proc.getOutParams(), new DeclarationInformation(
					hasSpec ? StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM, procId));
			
			newProc = new Procedure(proc.getLocation(), processAttributes(proc.getAttributes()), procId,
					proc.getTypeParams(), newInParams, newOutParams, newSpecs, newBody);
			ModelUtils.mergeAnnotations(proc, newProc);
		}
		mEdgeIndexStack.pop();
		mProcedureStack.pop();

		return newProc;
	}
	
	/** @return Identifier of the procedure, in which the inlining started. */
	private String getEntryProcId() {
		return mProcedureStack.peekLast().getId();
	}
	
	/** @return Identifier of the currently processed procedure. */
	private String currentProcId() {
		return mProcedureStack.peek().getId();
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

	/** @return The process takes place inside the entry procedure, according to the procedure stack. */
	private boolean inEntryProcedure() {
		return mProcedureStack.size() == 1;
	}

	/** @return The process takes place inside an old() expression, which was or will be inlined. */
	private boolean inInlinedOldExpr() {
		return !mInlinedOldExprStack.isEmpty();
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
	private void mapVariablesOfCurrentProcedure() throws CancelToolchainException {
		CallGraphNode proc = mProcedureStack.peek();
		Procedure procWithSpec = proc.getProcedureWithSpecification();
		Procedure procWithBody = proc.getProcedureWithBody();
		if (proc.isPolymorphic()) {
			throw new InlinePolymorphicException(procWithSpec.getLocation(), proc.getId()); // TODO move to another pos?
		}
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
	
	// call only once for each procedure
	private void mapProcedureParameters(Procedure proc) {
		boolean hasSpec = proc.getSpecification() != null;
		List<VarList> inlinedParams = new ArrayList<>(proc.getInParams().length + proc.getOutParams().length);
		StorageClass inStorageClass = hasSpec ? StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM;
		StorageClass outStorageClass = hasSpec ? StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM;
		inlinedParams.addAll(mapVariables(proc.getInParams(), inStorageClass));
		inlinedParams.addAll(mapVariables(proc.getOutParams(), outStorageClass));
		if (!inEntryProcedure() && inlinedParams.size() > 0) {
			Attribute[] newAttrs = {}; // Parameters can't have Attributes
			VarList[] newVarLists = new VarList[inlinedParams.size()];
			inlinedParams.toArray(newVarLists);
			VariableDeclaration newVarDecl = new VariableDeclaration(proc.getLocation(), newAttrs, newVarLists);
			mInlinedVars.add(newVarDecl);
		}
	}
	
	/**
	 * ...
	 * @param inParams The given VarLists are input parameters of the procedure (false = output parameters).
	 */
	private void mapProcedureParametersToSameValue(VarList[] paramsProcDecl, VarList[] paramsProcImpl,
			boolean inParams) {
		boolean inEntryProc = inEntryProcedure();
		String originalProcId = currentProcId();
		String entryProcId = getEntryProcId();
		StorageClass storageClassProcDecl =
				inParams ? StorageClass.PROC_FUNC_INPARAM : StorageClass.PROC_FUNC_OUTPARAM;
		StorageClass storageClassProcImpl =
				inParams ? StorageClass.IMPLEMENTATION_INPARAM : StorageClass.IMPLEMENTATION_OUTPARAM;
		DeclarationInformation oldDeclInfoProcDecl = new DeclarationInformation(storageClassProcDecl, originalProcId);
		DeclarationInformation oldDeclInfoProcImpl = new DeclarationInformation(storageClassProcImpl, originalProcId);
		DeclarationInformation newDeclInfoProcDecl = new DeclarationInformation(
				inEntryProc ? storageClassProcDecl : StorageClass.LOCAL, entryProcId);
		DeclarationInformation newDeclInfoProcImpl = new DeclarationInformation(
				inEntryProc ? storageClassProcImpl : StorageClass.LOCAL, entryProcId);

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
				newParamId = mVarIdManager.makeAndAddUniqueId(usedParamId);
			} else {
				newParamId = mVarIdManager.makeAndAddUniqueId(originalProcId, usedParamId);				
			}
			VarMapKey keyProcDecl = new VarMapKey(iterator.currentId(gProcDecl), oldDeclInfoProcDecl);
			VarMapKey keyProcImpl = new VarMapKey(iterator.currentId(gProcImpl), oldDeclInfoProcImpl);
			mVarMap.put(keyProcDecl, new VarMapValue(newParamId, newDeclInfoProcDecl));
			mVarMap.put(keyProcImpl, new VarMapValue(newParamId, newDeclInfoProcImpl));
			
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
		// quantified vars don't have to be added to the inlined local variables,
		// because they don't have to be defined as local variables
	}

	/**
	 * Adds a mapping for a variable, that is inside an inlined old() expressions.
	 * Nothing is changed if the mapping already existed.
	 * Variables which are not affect by old() (local variables, for instance) are mapped to the existing value
	 * from the mapping without old() expressions.
	 * @param idExpr IdentifierExpression to be mapped.
	 * 
	 * @see #inInlinedOldExpr(DeclarationInformation)
	 */
	private void mapVariableInInlinedOldExpr(IdentifierExpression idExpr) {
		String id = idExpr.getIdentifier();
		String procId = currentProcId();
		DeclarationInformation declInfo = idExpr.getDeclarationInformation();
		VarMapKey keyWithOld = new VarMapKey(id, declInfo, procId);
		if (!mVarMap.containsKey(keyWithOld)) {
			VarMapValue value = null;
			if (declInfo.getStorageClass() == StorageClass.GLOBAL) {
				// Create mapping
				DeclarationInformation newDeclInfo = new DeclarationInformation(StorageClass.LOCAL, getEntryProcId());
				String newId = mVarIdManager.makeAndAddUniqueId(procId + "_old", id);
				value = new VarMapValue(newId, newDeclInfo);
				// Declare as local variable
				Declaration origVarDecl = mGlobalScopeManager.getVarDeclaration(id);
				VarList origVarList = mGlobalScopeManager.getVarListFromDeclaration(id);
				Attribute[] newAttributes = processAttributes(origVarDecl.getAttributes());
				ASTType type = origVarList.getType();
				// TODO Are the used ILocations intuitive?
				VarList[] newVarLists = { new VarList(origVarList.getLocation(), new String[] { newId }, type) };
				mInlinedVars.add(new VariableDeclaration(origVarDecl.getLocation(), newAttributes, newVarLists));
				mInlinedOldVarStack.peek().add(
						new VariableLHS(mInlinedOldExprStack.peek().getLocation(), type.getBoogieType(), id,
						new DeclarationInformation(StorageClass.GLOBAL, null)));
			} else {
				VarMapKey keyWithoutOld = new VarMapKey(id, declInfo);
				value = mVarMap.get(keyWithoutOld);
			}
			mVarMap.put(keyWithOld, value);
		}
	}
	
	/**
	 * Generates new unique identifiers for variables and updates the map.
	 * This method is only for VarLists that are part of a procedure (no global variables for instance).
	 * @param varLists Variables to be processed (must be part of a procedure).
	 * @param storageClass Original StorageClass of the variables.
	 * @return List of VarLists, with new names and the same types.
	 * 		   Use this to inline the processed variables as local variables.
	 */
	private List<VarList> mapVariables(VarList[] varLists, StorageClass storageClass) {
		boolean inEntryProcedure = inEntryProcedure();
		String entryProcId = getEntryProcId();
		String originalProcId = currentProcId();
		boolean isQuantified = (storageClass == StorageClass.QUANTIFIED);
		String oldDeclInfoProcId = isQuantified ? null : originalProcId;
		DeclarationInformation oldDeclInfo = new DeclarationInformation(storageClass, oldDeclInfoProcId);
		DeclarationInformation newDeclInfo;
		if (inEntryProcedure) {
			newDeclInfo = oldDeclInfo;
		} else {
			StorageClass newStorageClass = isQuantified ? StorageClass.QUANTIFIED : StorageClass.LOCAL;
			String newDeclInfoProcId = isQuantified ? null : entryProcId;
			newDeclInfo = new DeclarationInformation(newStorageClass, newDeclInfoProcId);
		}
		List<VarList> newVarLists = new ArrayList<>();
		for (VarList varList : varLists) {
			List<String> newVarIds = new ArrayList<>();
			for (String varId : varList.getIdentifiers()) {
				String newVarId;
				if (inEntryProcedure) {
					newVarId = mVarIdManager.makeAndAddUniqueId(varId);
				} else {
					// DeclarationInformations of quantified vars contain no procedure, hence the prefix doesn't too.
					String prefix = isQuantified ? "quantified" : originalProcId;
					newVarId = mVarIdManager.makeAndAddUniqueId(prefix, varId);
					newVarIds.add(newVarId);
				}
				VarMapKey key = new VarMapKey(varId, oldDeclInfo);
				VarMapValue value = new VarMapValue(newVarId, newDeclInfo);
				// quantified vars with the same id could be already mapped -- don't change the mapping for them!
				if (!mVarMap.containsKey(key)) {
					mVarMap.put(key, value);					
				} else if (!isQuantified) {
					throw new AssertionError("A variable wasn't mapped properly: " + key);
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

	private Statement[] flattenStatementsArray(Statement[] stats) throws CancelToolchainException {
		List<Statement> flatStats = flattenStatements(stats);
		return flatStats.toArray(new Statement[flatStats.size()]);
	}
	
	private List<Statement> flattenStatements(Statement[] stats) throws CancelToolchainException {
		List<Statement> newStats = new ArrayList<Statement>();
		for (Statement stat : stats) {
			newStats.addAll(flattenStatement(stat));
		}
		return newStats;
	}
	
	private List<Statement> flattenStatement(Statement stat) throws CancelToolchainException {
		Statement newStat = null;
		if (stat instanceof CallStatement) {
			CallStatement call = (CallStatement) stat;
			int edgeIndex = getAndUpdateEdgeIndex();
			CallGraphNode callerNode = mProcedureStack.peek();
			CallGraphNode calleeNode = callerNode.getOutgoingNodes().get(edgeIndex);
			CallGraphEdgeLabel edgeLabel = callerNode.getOutgoingEdgeLabels().get(edgeIndex);
			assert call.getMethodName().equals(calleeNode.getId())
				&& call.getMethodName().equals(edgeLabel.getCalleeProcedureId());
			if (edgeLabel.getInlineFlag()) {
				mProcedureStack.push(calleeNode);
				mEdgeIndexStack.push(0);
				if (incrementCallCounter(calleeNode.getId()) <= 0) {
					mapVariablesOfCurrentProcedure();
				}
				List<Statement> inlinedCall;
				if (call.isForall()) {
					inlinedCall = inlineCallForall(call, calleeNode);
				} else {
					inlinedCall = inlineCall(call, calleeNode);
				}
				mEdgeIndexStack.pop();
				mProcedureStack.pop();
				return inlinedCall;
			}
		} else if (stat instanceof IfStatement) {
			IfStatement ifStat = (IfStatement) stat;
			Expression newCond = processExpression(ifStat.getCondition());
			Statement[] newThens = flattenStatementsArray(ifStat.getThenPart());
			Statement[] newElses = flattenStatementsArray(ifStat.getElsePart());
			newStat = new IfStatement(ifStat.getLocation(), newCond, newThens, newElses);
		} else if (stat instanceof WhileStatement) {
			WhileStatement whileStat = (WhileStatement) stat;
			Expression newCond = processExpression(whileStat.getCondition());
			LoopInvariantSpecification[] newInvs = processLoopSpecifications(whileStat.getInvariants());
			Statement[] newBody = flattenStatementsArray(whileStat.getBody());
			newStat = new WhileStatement(whileStat.getLocation(), newCond, newInvs, newBody);
		}
		if (newStat == null) {
			newStat = processStatement(stat);
		} else {
			ModelUtils.mergeAnnotations(stat, newStat);			
		}
		return Collections.singletonList(newStat);
	}
	
	private List<Statement> inlineCallForall(CallStatement call, CallGraphNode calleeNode) {
		throw new UnsupportedOperationException("Call forall isn't supported yet."); // TODO support
	}

	private List<Statement> inlineCall(CallStatement call, CallGraphNode calleeNode) throws CancelToolchainException {
		VariableLHS[] processedCallLHS = processVariableLHSs(call.getLhs());
		
		mInlinedOldVarStack.push(new ArrayList<VariableLHS>());
		if (stackContainsDuplicates()) {
			throw new InlineRecursiveCallException(call);
		}

		// --------- inline specifications ---------
		Specification[] specs = calleeNode.getProcedureWithSpecification().getSpecification();
		List<Statement> assertRequires = new ArrayList<>();
		List<Statement> assumeRequires = new ArrayList<>();
		List<Statement> assertEnsures = new ArrayList<>();
		List<Statement> assumeEnsures = new ArrayList<>();
		List<ModifiesSpecification> modifiesSpecifications = new ArrayList<>();
		for (Specification spec : processSpecifications(specs)) {
			ILocation loc = spec.getLocation();
			boolean isFree = spec.isFree();
			if (spec instanceof RequiresSpecification) {
				Expression formula = ((RequiresSpecification) spec).getFormula();
				if (!isFree) {
					AssertStatement assertStat = new AssertStatement(loc, formula);
					ModelUtils.mergeAnnotations(spec, assertStat);
					assertRequires.add(assertStat);					
				}
				if (isFree || mAssumeRequiresAfterAssert) {
					AssumeStatement assumeStat = new AssumeStatement(loc, formula);
					ModelUtils.mergeAnnotations(spec, assumeStat);
					assumeRequires.add(assumeStat);
				}
			} else if (spec instanceof EnsuresSpecification) {
				Expression formula = ((EnsuresSpecification) spec).getFormula();
				if (!isFree && mAssertEnsuresBeforeAssume && calleeNode.isImplemented()) {
					AssertStatement assertStat = new AssertStatement(loc, formula);
					ModelUtils.mergeAnnotations(spec, assertStat);
					assertEnsures.add(assertStat);
				}
				AssumeStatement assumeStat = new AssumeStatement(loc, formula);
				ModelUtils.mergeAnnotations(spec, assumeStat);
				assumeEnsures.add(assumeStat);
			} else if (spec instanceof ModifiesSpecification) {
				modifiesSpecifications.add((ModifiesSpecification) spec);
			}
		}

		// --------- inline body (or havoc, if unimplemented) ---------
		ILocation callLocation = call.getLocation();
		Procedure proc;
		List<Statement> inlinedBody = new ArrayList<>();
		if (calleeNode.isImplemented()) {
			proc = calleeNode.getProcedureWithBody();
			ILocation procLocation = proc.getLocation();
			Body body = proc.getBody();
			Statement[] block = body.getBlock();
			mapLabels(block);
			mapReturnLabel();
			
			// havoc local variables from inlined procedure (they are reused for different calls)
			if (body.getLocalVars().length > 0) {
				List<VariableLHS> localVarLHS = new ArrayList<>();
				DeclarationInformation localDeclInfo =
						new DeclarationInformation(StorageClass.LOCAL, proc.getIdentifier());
				for (VariableDeclaration varDecl : body.getLocalVars()) {
					ILocation varDeclLocation = varDecl.getLocation();
					for (VarList varList : varDecl.getVariables()) {
						IType varListType = varList.getType().getBoogieType();
						for (String varId : varList.getIdentifiers()) {
							localVarLHS.add(new VariableLHS(varDeclLocation, varListType, varId, localDeclInfo));
						}
					}
				}
				inlinedBody.add(processStatement(
						new HavocStatement(callLocation, localVarLHS.toArray(new VariableLHS[localVarLHS.size()]))));
			}

			// inline body
			for (Statement stat : block) {
				inlinedBody.addAll(flattenStatement(stat));
			}
			// insert end label (ReturnStatements are inlined as jumps to this label)
			Label returnLabel = new Label(proc.getLocation(), getCurrentReturnLabelId());
			inlinedBody.add(returnLabel);

		} else { // unimplemented procedure

			proc = calleeNode.getProcedureWithSpecification();
			for (ModifiesSpecification modSpec : modifiesSpecifications) {
				Statement havocModifiedVars = processStatement(
						new HavocStatement(modSpec.getLocation(), modSpec.getIdentifiers()));
				ModelUtils.mergeAnnotations(modSpec, havocModifiedVars);
				inlinedBody.add(havocModifiedVars);
			}
			if (processedCallLHS.length > 0) {
				inlinedBody.add(new HavocStatement(proc.getLocation(), processedCallLHS));				
			}
		}
		ILocation procLocation = proc.getLocation();
		boolean procHasSpec = (proc.getSpecification() != null);

		// --------- assign call arguments to in-parameters ---------
		List<Statement> writeToInParams = new ArrayList<>();
		if (proc.getInParams().length > 0) {
			Expression[] inVarRHSs = call.getArguments();
			VariableLHS[] inVarLHSs = new VariableLHS[inVarRHSs.length];
			VarListIterator inParamsIterator = new VarListIterator(proc.getInParams());
			DeclarationInformation inParamDeclInfo = new DeclarationInformation(procHasSpec ?
					StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM,
					calleeNode.getId());
			for (int i = 0; i < inVarRHSs.length; ++i) {
				inParamsIterator.next();
				IType inParamType = inParamsIterator.currentVarList(0).getType().getBoogieType();
				String inParamId = inParamsIterator.currentId(0);
				inVarLHSs[i] = new VariableLHS(proc.getLocation(), inParamType, inParamId, inParamDeclInfo);
			}
			writeToInParams.add(processStatement(new AssignmentStatement(callLocation, inVarLHSs, inVarRHSs)));
		}
		
		// --------- assign out-parameters to target variables from call statement ---------
		List<Statement> writeFromOutParams = new ArrayList<>();
		if (proc.getOutParams().length > 0) {
			Expression[] processedOutParamRHS = new Expression[processedCallLHS.length];
			VarListIterator outParamsIterator = new VarListIterator(proc.getOutParams());
			DeclarationInformation outParamDeclInfo = new DeclarationInformation(procHasSpec ?
					StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM,
					calleeNode.getId());
			for (int i = 0; i < processedCallLHS.length; ++i) {
				outParamsIterator.next();
				IType outParamType = outParamsIterator.currentVarList(0).getType().getBoogieType();
				String outParamId =  outParamsIterator.currentId(0);
				processedOutParamRHS[i] = processExpression(
						new IdentifierExpression(procLocation, outParamType, outParamId, outParamDeclInfo));
			}
			writeFromOutParams .add(new AssignmentStatement(callLocation, processedCallLHS, processedOutParamRHS));
		}
		
		// --------- keep old state of global vars, which appear inside old() expressions ---------
		List<VariableLHS> oldVars = mInlinedOldVarStack.pop();
		DeclarationInformation declInfoGlobal = new DeclarationInformation(StorageClass.GLOBAL, null);
		VariableLHS[] oldVarLHS = new VariableLHS[oldVars.size()];
		Expression[] oldVarRHS = new Expression[oldVars.size()];
		for (int i = 0; i < oldVars.size(); ++i) {
			VariableLHS oldVar = oldVars.get(i);
			VarMapKey oldVarKey = new VarMapKey(oldVar.getIdentifier(), declInfoGlobal, proc.getIdentifier());
			VarMapValue mapping = mVarMap.get(oldVarKey);
			oldVarLHS[i] = new VariableLHS(callLocation, oldVar.getType(),
					mapping.getVarId(), mapping.getDeclInfo());
			oldVarRHS[i] = new IdentifierExpression(callLocation, oldVar.getType(),
					oldVar.getIdentifier(), oldVar.getDeclarationInformation());
		}
		
		// --------- build the block to be inserted instead of the call ---------
		List<Statement> inlineBlock = new ArrayList<>();
		if (oldVarLHS.length > 0) {
			inlineBlock.add(new AssignmentStatement(callLocation, oldVarLHS, oldVarRHS)); // safe global variables			
		}
		// note: some lists may be empty
		inlineBlock.addAll(writeToInParams);
		inlineBlock.addAll(assertRequires);
		inlineBlock.addAll(assumeRequires);
		inlineBlock.addAll(inlinedBody);
		inlineBlock.addAll(assertEnsures);
		inlineBlock.addAll(assumeEnsures);
		inlineBlock.addAll(writeFromOutParams);

		return inlineBlock;
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
			if (label != null) {
				newStatement = new BreakStatement(breakStat.getLocation(), getNewLabelId(label));				
			}
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
	
	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		LeftHandSide newLhs = null;
		if (lhs instanceof VariableLHS) {
			VariableLHS varLhs = (VariableLHS) lhs;
			String id = varLhs.getIdentifier();
			DeclarationInformation declInfo = varLhs.getDeclarationInformation();
			VarMapValue mapping = mVarMap.get(new VarMapKey(id, declInfo, inOldExprOfProc()));
			String newId = mapping.getVarId();
			DeclarationInformation newDeclInfo = mapping.getDeclInfo();
			if (id != newId || declInfo != newDeclInfo) {
				newLhs = new VariableLHS(varLhs.getLocation(), varLhs.getType(), newId, newDeclInfo);
			}
		} else if (lhs instanceof StructLHS) {
			StructLHS structLhs = (StructLHS) lhs;
			LeftHandSide structStruct = structLhs.getStruct();
			LeftHandSide newStructStruct = processLeftHandSide(structStruct);
			if (newStructStruct != structStruct) {
				newLhs = new StructLHS(structLhs.getLocation(), newStructStruct, structLhs.getField());
			}
		} else { // ArrayLHS is handled by the super implementation
			return super.processLeftHandSide(lhs);
		}
		if (newLhs == null) {
			return lhs;	
		} else {
			ModelUtils.mergeAnnotations(lhs, newLhs);
			return newLhs;
		}
	}
	
	private String getNewLabelId(String oldLabelId) {
		String procId = currentProcId();
		String newName = mLabelMap.get(new LabelMapKey(oldLabelId, procId, getCallCounter(procId)));
		assert newName != null : "Missing mapping for Label: " + oldLabelId;
		return newName;
	}

	private void mapReturnLabel() {
		String procId = currentProcId();
		String returnLabelId = mLabelIdManager.makeAndAddUniqueId(procId, "returnLabel");
		mLabelMap.put(createCurrentReturnLabelKey() , returnLabelId);
	}
	
	private String getCurrentReturnLabelId() {
		return mLabelMap.get(createCurrentReturnLabelKey());
	}
	
	private LabelMapKey createCurrentReturnLabelKey() {
		String procId = currentProcId();
		// we can use the call counter, because recursion is forbidden
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
			String procId = currentProcId();
			String labelId = ((Label) stat).getName();
			String newLabelId;
			if (inEntryProcedure()) {
				newLabelId = mLabelIdManager.addId(labelId);
			} else {
				newLabelId = mLabelIdManager.makeAndAddUniqueId(procId, labelId);				
			}
			LabelMapKey key = new LabelMapKey(labelId, procId, getCallCounter(procId));
			mLabelMap.put(key, newLabelId);
		}
	}
	
	@Override
	protected Expression processExpression(Expression expr) {
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression idExpr = (IdentifierExpression) expr;
			String id = idExpr.getIdentifier();
			DeclarationInformation declInfo = idExpr.getDeclarationInformation();
			String inOldExprOfProc = inOldExprOfProc();
			if (inOldExprOfProc != null) {
				mapVariableInInlinedOldExpr(idExpr);	
			}
			VarMapValue mapping = mVarMap.get(new VarMapKey(id, declInfo, inOldExprOfProc));
			String newId = mapping.getVarId();
			DeclarationInformation newDeclInfo = mapping.getDeclInfo();
			if (newId != id || newDeclInfo != declInfo) {
				IdentifierExpression newIdExpr = new IdentifierExpression(
						idExpr.getLocation(), idExpr.getType(), newId, newDeclInfo);
				ModelUtils.mergeAnnotations(idExpr, newIdExpr);
				return newIdExpr;
			} else {
				return idExpr;
			}
		} else if (expr instanceof UnaryExpression
				&& ((UnaryExpression) expr).getOperator() == UnaryExpression.Operator.OLD
				&& !inEntryProcedure()) {
			UnaryExpression unaryExpr = (UnaryExpression) expr;
			mInlinedOldExprStack.push(unaryExpr);
			Expression newExpr = processExpression(unaryExpr.getExpr());
			mInlinedOldExprStack.pop();
			ModelUtils.mergeAnnotations(unaryExpr, newExpr); // TODO is this good or bad?
			return newExpr;
		} else if (expr instanceof QuantifierExpression) {
			throw new UnsupportedOperationException("Quantifiers aren't supported yet."); // TODO support
		} else {
			return super.processExpression(expr);
		}
	}
	
	protected VarList[] applyMappingToVarList(VarList vls[], DeclarationInformation declInfo) {
		VarList[] newVls = new VarList[vls.length];
		boolean changed = false;
		for (int i = 0; i < vls.length; ++i) {
			VarList vl = vls[i];
			VarList newVl = applyMappingToParameters(vl, declInfo);
			if (newVl != vl) {
				changed = true;
			}
			newVls[i] = newVl;
		}
		return changed ? newVls : vls;
	}
	
	protected VarList applyMappingToParameters(VarList vl, DeclarationInformation declInfo) {
		Expression where = vl.getWhereClause();
		Expression newWhere = where != null ? processExpression(where) : null;
		String[] ids = vl.getIdentifiers();
		String[] newIds = processVarIds(ids, declInfo);
		if (newWhere != where || ids != newIds) {
			VarList newVl = new VarList(vl.getLocation(), newIds, vl.getType(), newWhere);
			ModelUtils.mergeAnnotations(vl, newVl);
			return newVl;
		}
		return vl;
	}
	
	private String[] processVarIds(String[] ids, DeclarationInformation declInfo) {
		String[] newIds = new String[ids.length];
		boolean changed = false;
		for (int i = 0; i < ids.length; ++i) {
			String id = ids[i];
			String newId = mVarMap.get(new VarMapKey(id, declInfo, inOldExprOfProc())).getVarId();
			if (!newId.equals(id)) {
				changed = true;
			}
			newIds[i] = newId;
		}
		return changed ? newIds : ids;
	}
	
	/**
	 * Creates the last argument for the constructor of VarMapKey.
	 * @return Current procedure identifier, if processing takes place inside an inlined old() expression,
	 *         {@code null} otherwise.
	 */
	private String inOldExprOfProc() {
		if (inInlinedOldExpr()) {
			return currentProcId();
		} else {
			return null;
		}
	}


}
