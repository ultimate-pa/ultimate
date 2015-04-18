package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions.CancelToolchainException;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions.InliningUnsupportedException;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences.PreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.model.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.*;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Transforms a Boogie Procedure into an equivalent version, where contained calls are inlined.
 * Inlining of CallStatements ca be enabled/disabled, using {@link CallGraphEdgeLabel#setInlineFlag(boolean)}.
 * An instance of this class should be used only once.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class InlineVersionTransformer extends BoogieCopyTransformer {

	/**
	 * Used to manage Declarations which aren't changed, but have an effect on the inlining process.
	 * Instances of this class can and should be reused for different instances of the InlineVersionTransformer.
	 * 
	 * @author schaetzc@informatik.uni-freiburg.de
	 */
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

	private Logger mLogger;
	
	private GlobalScopeManager mGlobalScopeManager;
	
	/**
	 * The identifier from the entry procedure, which was inlined using this InlineVersionTransformer instance.
	 * null, if this InlineVersionTransformer instance wasn't used until now.
	 * Can be used to prohibit reuse of InlineVersionTransformer instances.
	 */
	private String mEntryProcId = null;

	/**
	 * Original CallStatements, which are currently inlined.
	 * Calls are pushed to the stack, whenever the inlining process starts, and popped again, when it ends.
	 * <p>
	 * Instead of just using one stack for calls, a stack of the described call stacks is used.
	 * Too push a call:
	 * <ul>
	 * <li> Copy the topmost inner stack.
	 * <li> Push the call onto the copied inner stack.
	 * <li> Push the copy onto the stack of stacks.
	 * </ul>
	 * <p>
	 * This behaviour allows to use the inner stacks directly for BackTransValues, without the need to copy them
	 * for every BackTransValue. It also ensures reference equality for equal call stacks.
	 * <p>
	 * Only used for backtranslation.
	 * 
	 * {@link #mProcedureStack} contains the called Procedures.
	 */
	private Deque<Deque<CallStatement>> mCallStackStack = new ArrayDeque<>(
			Collections.<Deque<CallStatement>>singleton(new ArrayDeque<CallStatement>()));

	/**
	 * Mapping from the new generated ASTNodes to their unprocessed origins.
	 * Only used for backtranslation.
	 */
	private Map<BoogieASTNode, BackTransValue> mBackTransMap = new HashMap<>();
	
	/**
	 * Similar to a call stack on execution, this contains the currently processed procedures.
	 * The entry procedure is on the bottom of the stack.
	 * Procedures of {@code call forall} statements aren't pushed onto the stack.
	 * <p>
	 * The {@code process...()}-Methods will yield different results, depending on the contents of this stack.
	 * (Mappings differ from procedure to procedure).
	 * <p>
	 * {@link #mCallStackStack} contains the CallStatements, that called the Procedures.
	 */
	private Deque<CallGraphNode> mProcedureStack = new ArrayDeque<>();

	/**
	 * Contains the number of processed calls (in the order of the program)
	 * inside the procedures of {@link #mProcedureStack}.
	 */
	private Deque<Integer> mEdgeIndexStack = new ArrayDeque<>();
	
	/**
	 * Counts for each procedure, how much calls to this procedure where inlined (!) during the process.
	 * {@code call forall} statements count too. Non-inlined calls don't count!<br>
	 * The parameters and local variables of a Procedure are mapped, iff call counter > 0.
	 * <p>
	 * <b>Note:</b> This has nothing to do with the "single calls only" setting
	 * ({@link PreferenceItem#IGNORE_MULTIPLE_CALLED}. This counter is used to avoid re-mapping of already mapped
	 * variable ids, whereas the setting is applied using a separate counter on the call graph.
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
	 * <p>
	 * Nested inlined procedures need their own old-variables. The top of the stack contains the variables for the
	 * currently processed procedure.<br>
	 * The stored IdentiferExpression are the original Expressions from the inside of the old() expressions.
	 * If a global variable appeared multiple times in one ore more old() expressions, the IdentiferExpression from
	 * the first occurrence is used.
	 * <p>
	 * This stack is based on Procedures.
	 */
	private Deque<Set<IdExprWrapper>> mInlinedOldVarStack = new ArrayDeque<>();
	
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
	
	/**
	 * Assume the inlined "requires" specifications (preconditions) after they were asserted.
	 * Applies to both, implemented and unimplemented procedures.
	 */
	private boolean mAssumeRequiresAfterAssert;

	/**
	 * Assert the inlined "ensures" specifications (postconditions) before they are assumed.
	 * Applies only to implemented procedures.
	 */
	private boolean mAssertEnsuresBeforeAssume;
	
	/**
	 * Creates a new InlineVersionTransformer.
	 * @param services Services
	 * @param globalScopeManager GlobalScopeManager, has to be initialized already
	 * @param assumeRequiresAfterAssert Assume inlined preconditions after they were asserted.
	 * @param assertEnsuresBeforeAssume Assert inlined postconditions before they are assumed.
	 *                                  This setting applies only to implemented procedures.
	 */
	public InlineVersionTransformer(IUltimateServiceProvider services, GlobalScopeManager globalScopeManager,
			boolean assumeRequiresAfterAssert, boolean assertEnsuresBeforeAssume) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mGlobalScopeManager = globalScopeManager;
		mVarMap = globalScopeManager.initVarMap();
		globalScopeManager.initVarIdManager(mVarIdManager);
		mAssumeRequiresAfterAssert = assumeRequiresAfterAssert;
		mAssertEnsuresBeforeAssume = assertEnsuresBeforeAssume;
	}

	/**
	 * Creates an equivalent Procedure with inlined calls.
	 * Only marked calls will be inlined (see {@link CallGraphEdgeLabel#setInlineFlag(boolean)}.
	 * <p>
	 * The returned Procedure has an Specification, iff the original Procedure was combined.
	 * 
	 * @param entryNode Call graph node, representing the procedure to be flattened.
	 * @return Equivalent procedure with inlined calls. {@code null} for unimplemented procedures.
	 * 
	 * @throws CancelToolchainException If an error occurred and the toolchain should be canceled.
	 */
	public Procedure inlineCallsInside(CallGraphNode entryNode) throws CancelToolchainException {
		if (mEntryProcId != null) {
			throw new IllegalStateException("Instance was already used to inline an procedure: " + mEntryProcId);
		} else if (!entryNode.isImplemented()) {
			return null;
		}
		mEntryProcId = entryNode.getId();
		mProcedureStack.push(entryNode);
		mEdgeIndexStack.push(0);

		mapVariablesOfCurrentProcedure();

		Procedure proc = entryNode.getProcedureWithBody();
		String procId = proc.getIdentifier();
		Body body = proc.getBody();
		Statement[] block = body.getBlock();
		mapLabels(block);
		Statement[] newBlock = flattenStatementsArray(block);

		List<VariableDeclaration> newLocalVars = new ArrayList<>();
		DeclarationInformation localDeclInfo = new DeclarationInformation(StorageClass.LOCAL, procId);
		for (VariableDeclaration varDecl : body.getLocalVars()) {
			Attribute[] newAttrs = processAttributes(varDecl.getAttributes());
			VarList[] newVars = applyMappingToVarList(varDecl.getVariables(), localDeclInfo);
			VariableDeclaration newVarDecl = new VariableDeclaration(varDecl.getLocation(), newAttrs, newVars);
			ModelUtils.mergeAnnotations(varDecl, newVarDecl);
			newLocalVars.add(newVarDecl);
		}
		newLocalVars.addAll(mInlinedVars);
		VariableDeclaration[] newLocalVarsArray = newLocalVars.toArray(new VariableDeclaration[newLocalVars.size()]);
		Body newBody = new Body(body.getLocation(), newLocalVarsArray, newBlock);
		ModelUtils.mergeAnnotations(body, newBody);
		
		Specification[] oldSpecs = proc.getSpecification();
		boolean hasSpec = oldSpecs != null;
		Specification[] newSpecs = null;	
		if (hasSpec) {
			newSpecs = new Specification[oldSpecs.length];
			for (int i = 0; i < oldSpecs.length; ++i) {
				newSpecs[i] = processSpecification(oldSpecs[i]);
				addBacktranslation(newSpecs[i], oldSpecs[i]);
			}
		}
		
		VarList[] newInParams = applyMappingToVarList(proc.getInParams(), new DeclarationInformation(
				hasSpec ? StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM, procId));
		VarList[] newOutParams = applyMappingToVarList(proc.getOutParams(), new DeclarationInformation(
				hasSpec ? StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM, procId));
		
		Attribute[] newAttrs = processAttributes(proc.getAttributes());
		Procedure newProc = new Procedure(proc.getLocation(), newAttrs, procId, proc.getTypeParams(),
				newInParams, newOutParams, newSpecs, newBody);
		ModelUtils.mergeAnnotations(proc, newProc);

		mEdgeIndexStack.pop();
		mProcedureStack.pop();

		return newProc;
	}
	
	private void checkInstanceUsed() {
		if (mEntryProcId == null) {
			throw new IllegalStateException("Instance must have been used for inlining before.");
		}
	}
	
	/** @return Read-only view of the backtranslation map. */
	public Map<BoogieASTNode, BackTransValue> getBacktranslationMap() {
		checkInstanceUsed();
		return Collections.unmodifiableMap(mBackTransMap);
	}

	/** @return Read-only view of the variable map. */
	public Map<VarMapKey, VarMapValue> getVariableMap() {
		checkInstanceUsed();
		return Collections.unmodifiableMap(mVarMap);
	}
	
	/** @return Identifier of the procedure, in which the inlining started. */
	public String getEntryProcId() {
		checkInstanceUsed();
		return mEntryProcId;
	}

	/**
	 * Adds a backtranslation mapping for a BoogieASTNode.
	 * Use this for all Statements and Specifications.
	 * <p>
	 * There should be at most one inlined node, which maps to the original node,
	 * to avoid creation of duplicates in the backtranslation. 
	 * 
	 * @param inlinedNode The node, which should be backtranslateable.
	 * @param originalNode Original node, which created the inlined node.
	 *                     null, if the node should be neglected by the backtranslation.
	 */
	private void addBacktranslation(BoogieASTNode inlinedNode, BoogieASTNode originalNode) {
		mBackTransMap.put(inlinedNode, new BackTransValue(mEntryProcId, mCallStackStack.peek(), originalNode));
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
			ILocation location = proc.getProcedureWithSpecification().getLocation();
			throw new InliningUnsupportedException("Polymorphic procedure " + proc.getId(), location);
			// polymorphic procedures would need multiple mappings -- one for every call with other types
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
	
	
	/**
	 * Generates mappings for the parameters of combined procedures (declaration and implementation).
	 * This will updated {@link #mVarIdManager}, link #mVarMap}, {@link #mInlinedVars}.
	 * Call only once!
	 * 
	 * @param proc Combined procedure
	 */
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
	 * Generated mappings for the parameters of procedures with separate declaration and implementation.
	 * This will updated {@link #mVarIdManager}, link #mVarMap}, {@link #mInlinedVars}.
	 * The n-th variable from both lists will be mapped to the same value.
	 * Call once for in parameters and once for out parameters.
	 * 
	 * @param paramsProcDecl In or out parameters from the Procedure declaration
	 * @param paramsProcImpl In or out parameters from the Procedure implementation
	 * @param inParams The given VarLists are input parameters of the procedure (false = output parameters).
	 */
	private void mapProcedureParametersToSameValue(VarList[] paramsProcDecl, VarList[] paramsProcImpl,
			boolean inParams) {
		boolean inEntryProc = inEntryProcedure();
		String originalProcId = currentProcId();
		StorageClass storageClassProcDecl =
				inParams ? StorageClass.PROC_FUNC_INPARAM : StorageClass.PROC_FUNC_OUTPARAM;
		StorageClass storageClassProcImpl =
				inParams ? StorageClass.IMPLEMENTATION_INPARAM : StorageClass.IMPLEMENTATION_OUTPARAM;
		DeclarationInformation oldDeclInfoProcDecl = new DeclarationInformation(storageClassProcDecl, originalProcId);
		DeclarationInformation oldDeclInfoProcImpl = new DeclarationInformation(storageClassProcImpl, originalProcId);
		DeclarationInformation newDeclInfoProcDecl = new DeclarationInformation(
				inEntryProc ? storageClassProcDecl : StorageClass.LOCAL, mEntryProcId);
		DeclarationInformation newDeclInfoProcImpl = new DeclarationInformation(
				inEntryProc ? storageClassProcImpl : StorageClass.LOCAL, mEntryProcId);

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
				DeclarationInformation newDeclInfo = new DeclarationInformation(StorageClass.LOCAL, mEntryProcId);
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
			} else {
				VarMapKey keyWithoutOld = new VarMapKey(id, declInfo);
				value = mVarMap.get(keyWithoutOld);
			}
			mVarMap.put(keyWithOld, value);
		}
	}
	
	/**
	 * Updates {@link #mInlinedOldVarStack} for IdentifierExpressions from inside an old() expressions.
	 * If it is a global variable, it is added the the collection on top of the stack.
	 * @param idExpr unprocessed IdentifierExpressions from inside an old() expression.
	 */
	private void updateInlinedOldVarStack(IdentifierExpression idExpr) {
		if (idExpr.getDeclarationInformation().getStorageClass() == StorageClass.GLOBAL) {
			Set<IdExprWrapper> inlinedOldVars = mInlinedOldVarStack.peek();
			inlinedOldVars.add(new IdExprWrapper(idExpr));
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
		String originalProcId = currentProcId();
		boolean isQuantified = (storageClass == StorageClass.QUANTIFIED);
		String oldDeclInfoProcId = isQuantified ? null : originalProcId;
		DeclarationInformation oldDeclInfo = new DeclarationInformation(storageClass, oldDeclInfoProcId);
		DeclarationInformation newDeclInfo;
		if (inEntryProcedure) {
			newDeclInfo = oldDeclInfo;
		} else {
			StorageClass newStorageClass = isQuantified ? StorageClass.QUANTIFIED : StorageClass.LOCAL;
			String newDeclInfoProcId = isQuantified ? null : mEntryProcId;
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
			String[] newVarIdsArray = newVarIds.toArray(new String[newVarIds.size()]);
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
	
	private Deque<CallStatement> createUpdatedCallStack(CallStatement newestCall) {
		Deque<CallStatement> updatedCallStack = new ArrayDeque<CallStatement>(mCallStackStack.peek());
		updatedCallStack.push(newestCall);
		return updatedCallStack;
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
				VariableLHS[] processedCallLHSs = processVariableLHSs(call.getLhs());
				mCallStackStack.push(createUpdatedCallStack(call));
				mProcedureStack.push(calleeNode);
				mEdgeIndexStack.push(0);
				if (incrementCallCounter(calleeNode.getId()) <= 0) {
					mapVariablesOfCurrentProcedure();
				}
				List<Statement> inlinedCall = inlineCall(call, processedCallLHSs, calleeNode);
				mEdgeIndexStack.pop();
				mProcedureStack.pop();
				mCallStackStack.pop();
				if (call.getPayload().hasAnnotation()) {
					mLogger.warn("Discarded annotation of " + call + ": " + call.getPayload().getAnnotations());
				}
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
			newStat = processStatement(stat); // also adds backtranslation
		} else {
			ModelUtils.mergeAnnotations(stat, newStat);
			addBacktranslation(newStat, stat);
		}
		return Collections.singletonList(newStat);
	}

	/**
	 * Creates an inline version of a call.
	 * @code{call forall} statements aren't supported.
	 * 
	 * @param call Normal, unprocessed CallStatement which should be inlined.
	 * @param processedCallLHS Processed LHS of the CallStatement.
	 *                         The LHS instances from the array need to be unique for each call of this method.
	 * @param calleeNode CallGrapNode of the called procedure
	 * @return Inline version of the call.
	 * 
	 * @throws CancelToolchainException The program contained constructs which couldn't be inlined (e.g. recursion).
	 */
	private List<Statement> inlineCall(CallStatement call, VariableLHS[] processedCallLHS, CallGraphNode calleeNode)
			throws CancelToolchainException {

		mInlinedOldVarStack.push(new HashSet<IdExprWrapper>());

		String procId = calleeNode.getId();
		assert procId.equals(call.getMethodName());
		if (stackContainsDuplicates()) {
			throw new InliningUnsupportedException("Recursive call: " + call, call.getLocation());
		} else if (call.isForall()) {
			throw new InliningUnsupportedException("Call forall: " + call, call.getLocation());
		}

		// --------- inline specifications ---------
		Procedure procWithSpec = calleeNode.getProcedureWithSpecification();
		Specification[] specs = procWithSpec.getSpecification();
		List<Statement> assertRequires = new ArrayList<>();
		List<Statement> assumeRequires = new ArrayList<>();
		List<Statement> assertEnsures = new ArrayList<>();
		List<Statement> assumeEnsures = new ArrayList<>();
		List<ModifiesSpecification> unprocessedModSpecs = new ArrayList<>();
		for (Specification spec : specs) {
			Specification processedSpec = processSpecification(spec);
			ILocation loc = processedSpec.getLocation();
			boolean isFree = processedSpec.isFree();
			if (processedSpec instanceof RequiresSpecification) {
				Expression processedFormula = ((RequiresSpecification) processedSpec).getFormula();
				if (isFree) {
					throw new InliningUnsupportedException("Free ensures: " + call, call.getLocation()); 
				} else {
					AssertStatement assertStat = new AssertStatement(loc, processedFormula);
					ModelUtils.mergeAnnotations(processedSpec, assertStat);
					addBacktranslation(assertStat, spec);
					assertRequires.add(assertStat);
				}
				if (mAssumeRequiresAfterAssert) {
					AssumeStatement assumeStat = new AssumeStatement(loc, processedFormula);
					ModelUtils.mergeAnnotations(processedSpec, assumeStat);
					addBacktranslation(assumeStat, null); // "assert PRE" is always there and translates to the spec
					assumeRequires.add(assumeStat);
				}
			} else if (processedSpec instanceof EnsuresSpecification) {
				Expression formula = ((EnsuresSpecification) processedSpec).getFormula();
				if (!isFree && mAssertEnsuresBeforeAssume && calleeNode.isImplemented()) {
					AssertStatement assertStat = new AssertStatement(loc, formula);
					ModelUtils.mergeAnnotations(processedSpec, assertStat);
					addBacktranslation(assertStat, null); // "assume POST" is always there and translates to the spec
					assertEnsures.add(assertStat);
				}
				AssumeStatement assumeStat = new AssumeStatement(loc, formula);
				ModelUtils.mergeAnnotations(processedSpec, assumeStat);
				addBacktranslation(assumeStat, spec);
				assumeEnsures.add(assumeStat);
			} else if (processedSpec instanceof ModifiesSpecification) {
				unprocessedModSpecs.add((ModifiesSpecification) processedSpec);
			}
		}

		// --------- inline body (or havoc, if unimplemented) ---------
		ILocation callLocation = call.getLocation();
		Procedure proc;
		List<Statement> inlinedBody = new ArrayList<>();
		
		// havoc out-parameters (they are reused for different calls)
		VarList[] outParams = procWithSpec.getOutParams();
		if (outParams.length > 0) {
			DeclarationInformation declInfo = new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, procId);
			List<VariableLHS> outParamLHSs = varListsToVarLHSs(outParams, declInfo);
			if (outParamLHSs.size() > 0) {
				VariableLHS[] outParamLHSsArray = outParamLHSs.toArray(new VariableLHS[outParamLHSs.size()]);
				Statement havocOutParams = processStatement(new HavocStatement(callLocation, outParamLHSsArray));
				addBacktranslation(havocOutParams, null);
				inlinedBody.add(havocOutParams);
			}
		}

		if (calleeNode.isImplemented()) {
			proc = calleeNode.getProcedureWithBody();
			Body body = proc.getBody();
			Statement[] block = body.getBlock();
			mapLabels(block);
			mapReturnLabel();
			
			// havoc local variables (they are reused for different calls)
			List<VariableLHS> localVarLHS = new ArrayList<>();
			DeclarationInformation localDeclInfo = new DeclarationInformation(StorageClass.LOCAL, procId);
			for (VariableDeclaration varDecl : body.getLocalVars()) {
				localVarLHS.addAll(varListsToVarLHSs(varDecl.getVariables(), localDeclInfo));
			}
			if (localVarLHS.size() > 0) {
				VariableLHS[] localVarLHSArray = localVarLHS.toArray(new VariableLHS[localVarLHS.size()]);
				Statement havocLocalVars = processStatement(new HavocStatement(callLocation, localVarLHSArray));
				addBacktranslation(havocLocalVars, null);
				inlinedBody.add(havocLocalVars);
			}

			// inline body
			inlinedBody.addAll(flattenStatements(block));

			// insert end label (ReturnStatements are inlined as jumps to this label)
			Label returnLabel = new Label(proc.getLocation(), getCurrentReturnLabelId());
			addBacktranslation(returnLabel, null);
			inlinedBody.add(returnLabel);

		} else { // unimplemented procedure

			// havoc global variables from modifies specifications
			proc = calleeNode.getProcedureWithSpecification();
			for (ModifiesSpecification modSpec : unprocessedModSpecs) {
				ModifiesSpecification processedModSpec = (ModifiesSpecification) processSpecification(modSpec);
				VariableLHS[] processedModVars = processedModSpec.getIdentifiers();
				if (processedModVars.length > 0) {
					Statement havocModifiedVars = new HavocStatement(processedModSpec.getLocation(), processedModVars);
					ModelUtils.mergeAnnotations(processedModSpec, havocModifiedVars);
					addBacktranslation(havocModifiedVars, modSpec); // TODO remove from backtranslated trace?
					inlinedBody.add(havocModifiedVars);
				}
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
			Statement assignStat = processStatement(new AssignmentStatement(callLocation, inVarLHSs, inVarRHSs));
			addBacktranslation(assignStat, null);
			writeToInParams.add(assignStat);
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
			Statement assignStat = new AssignmentStatement(callLocation, processedCallLHS, processedOutParamRHS);
			addBacktranslation(assignStat, null);
			writeFromOutParams .add(assignStat);
		}
		
		// --------- keep old state of global vars, which appear inside old() expressions ---------
		Set<IdExprWrapper> oldVars = mInlinedOldVarStack.pop();
		Iterator<IdExprWrapper> oldVarsIterator = oldVars.iterator();
		DeclarationInformation declInfoGlobal = new DeclarationInformation(StorageClass.GLOBAL, null);
		VariableLHS[] oldVarLHS = new VariableLHS[oldVars.size()];
		Expression[] oldVarRHS = new Expression[oldVars.size()];
		for (int i = 0; oldVarsIterator.hasNext(); ++i) {
			IdentifierExpression idExpr = oldVarsIterator.next().getIdExpr();
			String id = idExpr.getIdentifier();
			IType type = idExpr.getType();
			VarMapValue mapping = mVarMap.get(new VarMapKey(id, declInfoGlobal, proc.getIdentifier()));
			oldVarLHS[i] = new VariableLHS(callLocation, type, mapping.getVarId(), mapping.getDeclInfo());
			oldVarRHS[i] = new IdentifierExpression(callLocation, type, id, declInfoGlobal);
		}
		
		// --------- build the block to be inserted instead of the call ---------
		List<Statement> inlineBlock = new ArrayList<>();
		if (oldVarLHS.length > 0) {
			// safe global variables
			Statement assignStat = new AssignmentStatement(callLocation, oldVarLHS, oldVarRHS);
			addBacktranslation(assignStat, null);
			inlineBlock.add(assignStat);
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
	
	private List<VariableLHS> varListsToVarLHSs(VarList[] varLists, DeclarationInformation declInfo) {
		List<VariableLHS> varLHSs = new ArrayList<>(3 * varLists.length);
		for (VarList varList : varLists) {
			IType type = varList.getType().getBoogieType();
			ILocation location = varList.getLocation();
			for (String id : varList.getIdentifiers()) {
				varLHSs.add(new VariableLHS(location, type, id, declInfo));
			}
		}
		return varLHSs;
	}
	
	@Override
	protected Statement processStatement(Statement stat) {
		Statement newStat = null;
		if (stat instanceof Label) {
			Label label = (Label) stat;
			newStat = new Label(label.getLocation(), getNewLabelId(label.getName()));
		} else if (stat instanceof GotoStatement) {
			GotoStatement gotoStat = (GotoStatement) stat;
			String[] labelIds = gotoStat.getLabels();
			String[] newLabelIds = new String[labelIds.length];
			for (int i = 0; i < labelIds.length; ++i) {
				newLabelIds[i] = getNewLabelId(labelIds[i]);
			}
			newStat = new GotoStatement(gotoStat.getLocation(), newLabelIds);
		} else if (stat instanceof BreakStatement) {
			BreakStatement breakStat = (BreakStatement) stat;
			String label = breakStat.getLabel();
			if (label != null) {
				newStat = new BreakStatement(breakStat.getLocation(), getNewLabelId(label));				
			}
		} else if (stat instanceof ReturnStatement && !inEntryProcedure()) {
			newStat = new GotoStatement(stat.getLocation(), new String[] { getCurrentReturnLabelId() });
		}
		if (newStat == null) {
			newStat = super.processStatement(stat);
		} else {
			ModelUtils.mergeAnnotations(stat, newStat);
		}
		addBacktranslation(newStat, stat);
		return newStat;
	}
	
	@Override
	protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
		LeftHandSide newLhs = null;
		if (lhs instanceof VariableLHS) {
			VariableLHS varLhs = (VariableLHS) lhs;
			DeclarationInformation declInfo = varLhs.getDeclarationInformation();
			VarMapValue mapping = mVarMap.get(new VarMapKey(varLhs.getIdentifier(), declInfo, inOldExprOfProc()));
			String newId = mapping.getVarId();
			DeclarationInformation newDeclInfo = mapping.getDeclInfo();
			newLhs = new VariableLHS(varLhs.getLocation(), varLhs.getType(), newId, newDeclInfo);
		} else if (lhs instanceof StructLHS) {
			StructLHS structLhs = (StructLHS) lhs;
			LeftHandSide newStructStruct = processLeftHandSide(structLhs.getStruct());
			newLhs = new StructLHS(structLhs.getLocation(), newStructStruct, structLhs.getField());
		} else if (lhs instanceof ArrayLHS) {
			ArrayLHS arrayLhs = (ArrayLHS) lhs;
			LeftHandSide newArray = processLeftHandSide(arrayLhs.getArray());
			Expression[] newIndices = processExpressions(arrayLhs.getIndices());
			newLhs = new ArrayLHS(lhs.getLocation(), arrayLhs.getType(), newArray, newIndices);
		} else {
			throw new UnsupportedOperationException("Cannot process unknown LHS: " + lhs.getClass().getName());
		}
		ModelUtils.mergeAnnotations(lhs, newLhs);
		return newLhs;
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
		Expression newExpr = null;
		if (expr instanceof IdentifierExpression) {
			IdentifierExpression idExpr = (IdentifierExpression) expr;
			String id = idExpr.getIdentifier();
			DeclarationInformation declInfo = idExpr.getDeclarationInformation();
			String inOldExprOfProc = inOldExprOfProc();
			if (inOldExprOfProc != null) {
				mapVariableInInlinedOldExpr(idExpr); // includes check to avoid mapping of already mapped values	
				updateInlinedOldVarStack(idExpr);
			}
			VarMapValue mapping = mVarMap.get(new VarMapKey(id, declInfo, inOldExprOfProc));
			String newId = mapping.getVarId();
			DeclarationInformation newDeclInfo = mapping.getDeclInfo();
			newExpr = new IdentifierExpression(idExpr.getLocation(), idExpr.getType(), newId, newDeclInfo);
		} else if (expr instanceof QuantifierExpression) {
			QuantifierExpression quantExpr = (QuantifierExpression) expr;
			ILocation location = quantExpr.getLocation();
			IType type = quantExpr.getType();
			VarList[] params = quantExpr.getParameters();
			Attribute[] attrs = quantExpr.getAttributes();
			Expression formula = quantExpr.getSubformula();

			mapVariables(quantExpr.getParameters(), StorageClass.QUANTIFIED);
			// quantified vars don't have to be added to the inlined local variables,
			// because they don't have to be defined as local variables

			VarList[] newParams = applyMappingToVarList(params,
					new DeclarationInformation(StorageClass.QUANTIFIED, null));
			Attribute[] newAttrs = processAttributes(attrs);
			Expression newFormula = processExpression(formula);
			newExpr = new QuantifierExpression(location, type, quantExpr.isUniversal(), quantExpr.getTypeParams(),
					newParams, newAttrs, newFormula);
		} else if (expr instanceof UnaryExpression
				&& ((UnaryExpression) expr).getOperator() == UnaryExpression.Operator.OLD
				&& !inEntryProcedure()) {
			UnaryExpression unaryExpr = (UnaryExpression) expr;
			mInlinedOldExprStack.push(unaryExpr);
			newExpr = processExpression(unaryExpr.getExpr());
			mInlinedOldExprStack.pop();
		} 
		if (newExpr == null) {
			return super.processExpression(expr);			
		} else {
			ModelUtils.mergeAnnotations(expr, newExpr);
			return newExpr;
		}
	}

	/**
	 * Applies the mapping to a VarList. Intended for mapping of procedure parameters.
	 * This method should be used in place of {@linkplain #processVarLists(VarList[])}.

	 * @param vls Original VarLists.
	 * @param declInfo Original DeclarationInformation of the variables from the VarLists.
	 * @return Mapped VarLists (note: the DeclarationInformation might have changed too).
	 */
	protected VarList[] applyMappingToVarList(VarList vls[], DeclarationInformation declInfo) {
		VarList[] newVls = new VarList[vls.length];
		boolean changed = false;
		for (int i = 0; i < vls.length; ++i) {
			VarList vl = vls[i];
			VarList newVl = applyMappingToVarList(vl, declInfo);
			if (newVl != vl) {
				changed = true;
			}
			newVls[i] = newVl;
		}
		return changed ? newVls : vls;
	}
	
	/**
	 * Applies the mapping to a VarList. Intended for mapping of procedure parameters.
	 * This method should be used in place of {@linkplain #processVarList(VarList)}.
	 * 
	 * @param vl Original VarList.
	 * @param declInfo Original DeclarationInformation of the variables from the VarList.
	 * @return Mapped VarList (note: the DeclarationInformation might have changed too).
	 */
	private VarList applyMappingToVarList(VarList vl, DeclarationInformation declInfo) {
		Expression where = vl.getWhereClause();
		Expression newWhere = where != null ? processExpression(where) : null;
		String[] ids = vl.getIdentifiers();
		String[] newIds = applyMappingToVarIds(ids, declInfo);
		if (newWhere != where || ids != newIds) {
			VarList newVl = new VarList(vl.getLocation(), newIds, vl.getType(), newWhere);
			ModelUtils.mergeAnnotations(vl, newVl);
			return newVl;
		}
		return vl;
	}
	
	/**
	 * Applies the mapping to identifiers of variables.
	 * @param ids Original identifiers of variables.
	 * @param declInfo Original DeclarationInformation of the variables.
	 * @return Mapped Identifiers (note: the DeclarationInformation might have changed too).
	 */
	private String[] applyMappingToVarIds(String[] ids, DeclarationInformation declInfo) {
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
	 * Disabled due to parameters restriction of super class.
	 * We need more parameters for a correct mapping of the variables.
	 * @see #applyMappingToVarList(VarList, DeclarationInformation)
	 * @see #applyMappingToVarList(VarList[], DeclarationInformation)
	 */
	@Deprecated
	@Override
	protected VarList processVarList(VarList varList) {
		throw new UnsupportedOperationException("Use \"applyMappingToVarList(...)\" instead.");
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
