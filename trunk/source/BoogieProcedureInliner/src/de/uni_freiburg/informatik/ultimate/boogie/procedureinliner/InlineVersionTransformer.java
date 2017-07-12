/*
 * Copyright (C) 2015 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogieProcedureInliner plug-in.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogieProcedureInliner plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogieProcedureInliner plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogieProcedureInliner plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogieProcedureInliner plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BoogieASTNode;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.GotoStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Label;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ReturnStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphEdgeLabel;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.callgraph.CallGraphNode;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions.CancelToolchainException;
import de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.exceptions.InliningUnsupportedException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;

/**
 * Transforms a Boogie Procedure into an equivalent version, where contained calls are inlined. Inlining of
 * CallStatements can be enabled/disabled, using {@link CallGraphEdgeLabel#setInlineFlag(boolean)}. An instance of this
 * class should be used only once.
 *
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class InlineVersionTransformer extends BoogieCopyTransformer {

	/**
	 * Used to manage Declarations which aren't changed, but have an effect on the inlining process. Instances of this
	 * class can and should be reused for different instances of the InlineVersionTransformer.
	 *
	 * @author schaetzc@informatik.uni-freiburg.de
	 */
	public static class GlobalScopeManager {

		private final Map<VarMapKey, VarMapValue> mVarMap = new HashMap<>();

		/**
		 * Maps identifiers from global constants or variables to their Declarations. The values are either
		 * ConstDeclarations or VariableDeclarations.
		 */
		private final Map<String, Declaration> mVarDecls = new HashMap<>();

		/** Maps identifiers from global constants or variables to the VarLists from their Declarations. */
		private final Map<String, VarList> mVarLists = new HashMap<>();

		public GlobalScopeManager(final Collection<Declaration> nonProcedureDeclarations) {
			for (final Declaration decl : nonProcedureDeclarations) {
				if (decl instanceof ConstDeclaration) {
					final ConstDeclaration constDecl = (ConstDeclaration) decl;
					final VarList varList = constDecl.getVarList();
					addVarsOrConsts(varList);
					for (final String id : varList.getIdentifiers()) {
						mVarDecls.put(id, constDecl);
						mVarLists.put(id, varList);
					}
				} else if (decl instanceof VariableDeclaration) {
					final VariableDeclaration varDecl = (VariableDeclaration) decl;
					for (final VarList varList : varDecl.getVariables()) {
						addVarsOrConsts(varList);
						for (final String id : varList.getIdentifiers()) {
							mVarDecls.put(id, varDecl);
							mVarLists.put(id, varList);
						}
					}
				}
			}
		}

		private void addVarsOrConsts(final VarList varList) {
			final List<String> ids = new ArrayList<>();
			final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.GLOBAL, null);
			for (final String id : varList.getIdentifiers()) {
				final VarMapKey key = new VarMapKey(id, declInfo);
				final VarMapValue value = new VarMapValue(id, declInfo);
				mVarMap.put(key, value);
				ids.add(id);
			}
		}

		/** @return New map from global variables and constants to the same values. */
		public Map<VarMapKey, VarMapValue> initVarMap() {
			return new HashMap<>(mVarMap);
		}

		public void initVarIdManager(final IdManager varIdManager) {
			for (final VarMapKey globalVarKey : mVarMap.keySet()) {
				varIdManager.addId(globalVarKey.getVarId());
			}
		}

		/**
		 * Gets the Declaration, containing a given global variable or constant.
		 *
		 * @param id
		 *            Identifier of the global variable or constant.
		 * @return Declaration or null, if no global variable or constant had the given id. The Declaration is either of
		 *         type VariableDeclaration or ConstDeclaration.
		 */
		public Declaration getVarDeclaration(final String id) {
			return mVarDecls.get(id);
		}

		/**
		 * Gets the VarList from a VariableDeclaration or ConstDeclaration, containing a given global variable or
		 * constant.
		 *
		 * @param id
		 *            Identifier of the global variable or constant.
		 * @return VarList or null, if no global variable or constant had the given id.
		 */
		public VarList getVarListFromDeclaration(final String id) {
			return mVarLists.get(id);
		}
	}

	private final ILogger mLogger;

	private final IProgressMonitorService mProgressMonitorService;

	private final GlobalScopeManager mGlobalScopeManager;

	private final InlinerStatistic mInlinerStatistic;

	/**
	 * The identifier from the entry procedure, which was inlined using this InlineVersionTransformer instance. null, if
	 * this InlineVersionTransformer instance wasn't used until now. Can be used to prohibit reuse of
	 * InlineVersionTransformer instances.
	 */
	private String mEntryProcId = null;

	/**
	 * Original CallStatements, which are currently inlined. Calls are pushed to the stack, whenever the inlining
	 * process starts, and popped again, when it ends.
	 * <p>
	 * Instead of just using one stack for calls, a stack of the described call stacks is used. Too push a call:
	 * <ul>
	 * <li>Copy the topmost inner stack.
	 * <li>Push the call onto the copied inner stack.
	 * <li>Push the copy onto the stack of stacks.
	 * </ul>
	 * <p>
	 * This behaviour allows to use the inner stacks directly for BackTransValues, without the need to copy them for
	 * every BackTransValue. It also ensures reference equality for equal call stacks.
	 * <p>
	 * Only used for backtranslation.
	 *
	 * {@link #mProcedureStack} contains the called Procedures.
	 */
	private final Deque<Deque<CallStatement>> mCallStackStack =
			new ArrayDeque<>(Collections.<Deque<CallStatement>> singleton(new ArrayDeque<CallStatement>()));

	/**
	 * Mapping from the new generated ASTNodes to their unprocessed origins. Only used for backtranslation.
	 */
	private final Map<BoogieASTNode, BackTransValue> mBackTransMap = new HashMap<>();

	/**
	 * Similar to a call stack on execution, this contains the currently processed procedures. The entry procedure is on
	 * the bottom of the stack. Procedures of {@code call forall} statements aren't pushed onto the stack.
	 * <p>
	 * The {@code process...()}-Methods will yield different results, depending on the contents of this stack. (Mappings
	 * differ from procedure to procedure).
	 * <p>
	 * {@link #mCallStackStack} contains the CallStatements, that called the Procedures.
	 */
	private final Deque<CallGraphNode> mProcedureStack = new ArrayDeque<>();

	/**
	 * Contains the number of processed calls (in the order of the program) inside the procedures of
	 * {@link #mProcedureStack}.
	 */
	private final Deque<Integer> mEdgeIndexStack = new ArrayDeque<>();

	/**
	 * Counts for each procedure, how much calls to this procedure where inlined (!) during the process.
	 * {@code call forall} statements count too. Non-inlined calls don't count!<br>
	 * The parameters and local variables of a Procedure are mapped, iff call counter > 0.
	 * <p>
	 * <b>Note:</b> This has nothing to do with the "single calls only" setting
	 * ({@link de.uni_freiburg.informatik.ultimate.boogie.procedureinliner.preferences.PreferenceItem #IGNORE_MULTIPLE_CALLED}.
	 * This counter is used to avoid re-mapping of already mapped variable ids, whereas the setting is applied using a
	 * separate counter on the call graph.
	 */
	private final Map<String, Integer> mCallCounter = new HashMap<>();

	/**
	 * Contains the (possibly nested) "old(...)" expression(s), in which the processing takes place. Only old()
	 * expressions that are inlined (in other words: removed) are stored. This stack is based on Expressions.
	 */
	private final Deque<UnaryExpression> mInlinedOldExprStack = new ArrayDeque<>();

	/**
	 * Keeps track of global variables, which appeared inside inlined old() expressions.
	 * <p>
	 * Nested inlined procedures need their own old-variables. The top of the stack contains the variables for the
	 * currently processed procedure.<br>
	 * The stored IdentiferExpression are the original Expressions from the inside of the old() expressions. If a global
	 * variable appeared multiple times in one ore more old() expressions, the IdentiferExpression from the first
	 * occurrence is used.
	 * <p>
	 * This stack is based on Procedures.
	 */
	private final Deque<Set<IdExprWrapper>> mInlinedOldVarStack = new ArrayDeque<>();

	/** Variables which have to be added to the local variables of the entry point. */
	private final List<VariableDeclaration> mInlinedVars = new ArrayList<>();

	/** Mapping from original variable identifiers to new ones. */
	private final Map<VarMapKey, VarMapValue> mVarMap;

	/** Manages the used variable identifiers. */
	private final IdManager mVarIdManager = new IdManager();

	/** Mapping from the old label identifiers to new ones. */
	private final Map<LabelMapKey, String> mLabelMap = new HashMap<>();

	/** Manages the used label identifiers. */
	private final IdManager mLabelIdManager = new IdManager();

	/**
	 * Creates a new InlineVersionTransformer.
	 *
	 * @param services
	 *            Services
	 * @param globalScopeManager
	 *            GlobalScopeManager, has to be initialized already
	 * @param inlinerStatistic
	 *            Statistic, will be updated while inlining
	 */
	public InlineVersionTransformer(final IUltimateServiceProvider services,
			final GlobalScopeManager globalScopeManager, final InlinerStatistic inlinerStatistic) {
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mProgressMonitorService = services.getProgressMonitorService();
		mGlobalScopeManager = globalScopeManager;
		mInlinerStatistic = inlinerStatistic;
		mVarMap = globalScopeManager.initVarMap();
		globalScopeManager.initVarIdManager(mVarIdManager);
	}

	/**
	 * Creates an equivalent Procedure with inlined calls. Only marked calls will be inlined (see
	 * {@link CallGraphEdgeLabel#setInlineFlag(boolean)}.
	 * <p>
	 * The returned Procedure has an Specification, iff the original Procedure was combined.
	 *
	 * @param entryNode
	 *            Call graph node, representing the procedure to be flattened.
	 * @return Equivalent procedure with inlined calls. {@code null} for unimplemented procedures.
	 *
	 * @throws CancelToolchainException
	 *             If an error occurred and the toolchain should be canceled.
	 */
	public Procedure inlineCallsInside(final CallGraphNode entryNode) throws CancelToolchainException {
		if (mEntryProcId != null) {
			throw new IllegalStateException("Instance was already used to inline an procedure: " + mEntryProcId);
		} else if (!entryNode.isImplemented()) {
			return null;
		}
		mEntryProcId = entryNode.getId();
		mProcedureStack.push(entryNode);
		mEdgeIndexStack.push(0);

		mapVariablesOfCurrentProcedure();

		final Procedure proc = entryNode.getProcedureWithBody();
		final String procId = proc.getIdentifier();
		final Body body = proc.getBody();
		final Statement[] block = body.getBlock();
		mapLabels(block);
		final Statement[] newBlock = flattenStatementsArray(block);

		final List<VariableDeclaration> newLocalVars = new ArrayList<>();
		final DeclarationInformation localDeclInfo = new DeclarationInformation(StorageClass.LOCAL, procId);
		for (final VariableDeclaration varDecl : body.getLocalVars()) {
			final Attribute[] newAttrs = processAttributes(varDecl.getAttributes());
			final VarList[] newVars = applyMappingToVarList(varDecl.getVariables(), localDeclInfo);
			final VariableDeclaration newVarDecl = new VariableDeclaration(varDecl.getLocation(), newAttrs, newVars);
			ModelUtils.copyAnnotations(varDecl, newVarDecl);
			newLocalVars.add(newVarDecl);
		}
		newLocalVars.addAll(mInlinedVars);
		final VariableDeclaration[] newLocalVarsArray =
				newLocalVars.toArray(new VariableDeclaration[newLocalVars.size()]);
		final Body newBody = new Body(body.getLocation(), newLocalVarsArray, newBlock);
		ModelUtils.copyAnnotations(body, newBody);

		final Specification[] oldSpecs = proc.getSpecification();
		final boolean hasSpec = oldSpecs != null;
		Specification[] newSpecs = null;
		if (hasSpec) {
			newSpecs = new Specification[oldSpecs.length];
			for (int i = 0; i < oldSpecs.length; ++i) {
				newSpecs[i] = processSpecification(oldSpecs[i]);
				addBacktranslation(newSpecs[i], oldSpecs[i]);
			}
		}

		final VarList[] newInParams = applyMappingToVarList(proc.getInParams(), new DeclarationInformation(
				hasSpec ? StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM, procId));
		final VarList[] newOutParams = applyMappingToVarList(proc.getOutParams(), new DeclarationInformation(
				hasSpec ? StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM, procId));

		final Attribute[] newAttrs = processAttributes(proc.getAttributes());
		final Procedure newProc = new Procedure(proc.getLocation(), newAttrs, procId, proc.getTypeParams(), newInParams,
				newOutParams, newSpecs, newBody);
		ModelUtils.copyAnnotations(proc, newProc);

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
	 * Adds a backtranslation mapping for a BoogieASTNode. Use this for all Statements and Specifications.
	 * <p>
	 * There should be at most one inlined node, which maps to the original node, to avoid creation of duplicates in the
	 * backtranslation.
	 * <p>
	 * Already mapped values can be overwritten, by calling this method again.
	 *
	 * @param inlinedNode
	 *            The node, which should be backtranslateable.
	 * @param originalNode
	 *            Original node, which created the inlined node. null, if the node should be neglected by the
	 *            backtranslation.
	 */
	private void addBacktranslation(final BoogieASTNode inlinedNode, final BoogieASTNode originalNode) {
		mBackTransMap.put(inlinedNode, new BackTransValue(mEntryProcId, mCallStackStack.peek(), originalNode));
	}

	/** @return Identifier of the currently processed procedure. */
	private String currentProcId() {
		return mProcedureStack.peek().getId();
	}

	/**
	 * Searches the procedure stack for duplicates. A duplicate inside the stack only occurs in case of recursion.
	 *
	 * @return The procedure stack contained a duplicate.
	 */
	private boolean stackContainsDuplicates() {
		final Set<String> procIds = new HashSet<>();
		for (final CallGraphNode node : mProcedureStack) {
			if (!procIds.add(node.getId())) {
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
	 *
	 * @param procId
	 *            Identifier of the called procedure.
	 * @return Number of inlined calls to the procedure.
	 * @see #mCallCounter
	 */
	private int getCallCounter(final String procId) {
		final Integer callCounter = mCallCounter.get(procId);
		return callCounter == null ? 0 : callCounter;
	}

	/**
	 * Increments the call counter for a given procedure. Use this method, when a call is inlined.
	 *
	 * @param procId
	 *            Identifier of the procedure.
	 * @return Old call counter value of the procedure.
	 * @see #mCallCounter
	 */
	private int incrementCallCounter(final String procId) {
		final int oldValue = getCallCounter(procId);
		mCallCounter.put(procId, oldValue + 1);
		return oldValue;
	}

	/**
	 * Increments the edge index on top of the {@link #mEdgeIndexStack}.
	 *
	 * @return The edge index from the top of the stack, before it was incremented.
	 */
	private int getAndUpdateEdgeIndex() {
		final int edgeIndex = mEdgeIndexStack.pop();
		mEdgeIndexStack.push(edgeIndex + 1);
		return edgeIndex;
	}

	/** Map input parameters, output parameters and local variables of the current procedure. */
	private void mapVariablesOfCurrentProcedure() throws CancelToolchainException {
		final CallGraphNode proc = mProcedureStack.peek();
		final Procedure procWithSpec = proc.getProcedureWithSpecification();
		final Procedure procWithBody = proc.getProcedureWithBody();
		if (proc.isPolymorphic()) {
			final ILocation location = proc.getProcedureWithSpecification().getLocation();
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
			final Body body = procWithBody.getBody();
			for (final VariableDeclaration localVarDecl : body.getLocalVars()) {
				mapLocalVariables(localVarDecl);
			}
		} else {
			mapProcedureParameters(procWithSpec);
		}
	}

	/**
	 * Generates mappings for the parameters of combined procedures (declaration and implementation). This will updated
	 * {@link #mVarIdManager}, link #mVarMap}, {@link #mInlinedVars}. Call only once!
	 *
	 * @param proc
	 *            Combined procedure
	 */
	private void mapProcedureParameters(final Procedure proc) {
		final boolean hasSpec = proc.getSpecification() != null;
		final List<VarList> inlinedParams = new ArrayList<>(proc.getInParams().length + proc.getOutParams().length);
		final StorageClass inStorageClass =
				hasSpec ? StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM;
		final StorageClass outStorageClass =
				hasSpec ? StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM;
		inlinedParams.addAll(mapVariables(proc.getInParams(), inStorageClass));
		inlinedParams.addAll(mapVariables(proc.getOutParams(), outStorageClass));
		if (!inEntryProcedure() && !inlinedParams.isEmpty()) {
			final Attribute[] newAttrs = {}; // Parameters can't have Attributes
			final VarList[] newVarLists = new VarList[inlinedParams.size()];
			inlinedParams.toArray(newVarLists);
			final VariableDeclaration newVarDecl = new VariableDeclaration(proc.getLocation(), newAttrs, newVarLists);
			mInlinedVars.add(newVarDecl);
		}
	}

	/**
	 * Generated mappings for the parameters of procedures with separate declaration and implementation. This will
	 * updated {@link #mVarIdManager}, link #mVarMap}, {@link #mInlinedVars}. The n-th variable from both lists will be
	 * mapped to the same value. Call once for in parameters and once for out parameters.
	 *
	 * @param paramsProcDecl
	 *            In or out parameters from the Procedure declaration
	 * @param paramsProcImpl
	 *            In or out parameters from the Procedure implementation
	 * @param inParams
	 *            The given VarLists are input parameters of the procedure (false = output parameters).
	 */
	private void mapProcedureParametersToSameValue(final VarList[] paramsProcDecl, final VarList[] paramsProcImpl,
			final boolean inParams) {
		final boolean inEntryProc = inEntryProcedure();
		final String originalProcId = currentProcId();
		final StorageClass storageClassProcDecl =
				inParams ? StorageClass.PROC_FUNC_INPARAM : StorageClass.PROC_FUNC_OUTPARAM;
		final StorageClass storageClassProcImpl =
				inParams ? StorageClass.IMPLEMENTATION_INPARAM : StorageClass.IMPLEMENTATION_OUTPARAM;
		final DeclarationInformation oldDeclInfoProcDecl =
				new DeclarationInformation(storageClassProcDecl, originalProcId);
		final DeclarationInformation oldDeclInfoProcImpl =
				new DeclarationInformation(storageClassProcImpl, originalProcId);
		final DeclarationInformation newDeclInfoProcDecl =
				new DeclarationInformation(inEntryProc ? storageClassProcDecl : StorageClass.LOCAL, mEntryProcId);
		final DeclarationInformation newDeclInfoProcImpl =
				new DeclarationInformation(inEntryProc ? storageClassProcImpl : StorageClass.LOCAL, mEntryProcId);

		final List<VariableDeclaration> inlinedVars = new ArrayList<>();
		// indices
		final int gProcDecl = 0;
		final int gProcImpl = 1;
		final int gUsed = gProcImpl; // only one identifier and location can be used for the new variable
		final int gUnused = (gUsed + 1) % 2; // the remaining index
		final VarListIterator iterator = new VarListIterator(paramsProcDecl, paramsProcImpl);
		while (iterator.hasNext()) {
			iterator.next();

			// Map parameters of implementation and declaration to the same identifiers
			final String usedParamId = iterator.currentId(gUsed);
			String newParamId;
			if (inEntryProc) {
				newParamId = mVarIdManager.makeAndAddUniqueId(usedParamId);
			} else {
				newParamId = mVarIdManager.makeAndAddUniqueId(originalProcId, usedParamId);
			}
			final VarMapKey keyProcDecl = new VarMapKey(iterator.currentId(gProcDecl), oldDeclInfoProcDecl);
			final VarMapKey keyProcImpl = new VarMapKey(iterator.currentId(gProcImpl), oldDeclInfoProcImpl);
			mVarMap.put(keyProcDecl, new VarMapValue(newParamId, newDeclInfoProcDecl));
			mVarMap.put(keyProcImpl, new VarMapValue(newParamId, newDeclInfoProcImpl));

			if (!inEntryProc) {
				// Create local VariableDeclaration for inlining into entry procedure
				final VarList usedVarList = iterator.currentVarList(gUsed);
				final VarList unusedVarList = iterator.currentVarList(gUnused);
				final ILocation location = usedVarList.getLocation();
				final String[] identifiers = { newParamId };
				assert usedVarList.getType().getBoogieType().equals(unusedVarList.getType().getBoogieType());
				final ASTType type = usedVarList.getType();
				Expression whereClause = usedVarList.getWhereClause();
				if (whereClause != null) {
					whereClause = processExpression(whereClause);
				}
				final Attribute[] attrs = {};
				final VarList variables = new VarList(location, identifiers, type, whereClause);
				ModelUtils.copyAnnotations(usedVarList, variables);
				ModelUtils.copyAnnotations(unusedVarList, variables);
				inlinedVars.add(new VariableDeclaration(location, attrs, new VarList[] { variables }));
			}
		}
		mInlinedVars.addAll(inlinedVars);
	}

	private void mapLocalVariables(final VariableDeclaration varDecl) {
		final List<VarList> inlinedVars = mapVariables(varDecl.getVariables(), StorageClass.LOCAL);
		if (!inEntryProcedure()) {
			final Attribute[] newAttrs = processAttributes(varDecl.getAttributes());
			final VarList[] newVarLists = new VarList[inlinedVars.size()];
			inlinedVars.toArray(newVarLists);
			final VariableDeclaration newVarDecl =
					new VariableDeclaration(varDecl.getLocation(), newAttrs, newVarLists);
			ModelUtils.copyAnnotations(varDecl, newVarDecl);
			mInlinedVars.add(newVarDecl);
		}
	}

	/**
	 * Adds a mapping for a variable, that is inside an inlined old() expressions. Nothing is changed if the mapping
	 * already existed. Variables which are not affect by old() (local variables, for instance) are mapped to the
	 * existing value from the mapping without old() expressions.
	 *
	 * @param idExpr
	 *            IdentifierExpression to be mapped.
	 *
	 * @see #inInlinedOldExpr(DeclarationInformation)
	 */
	private void mapVariableInInlinedOldExpr(final IdentifierExpression idExpr) {
		final String id = idExpr.getIdentifier();
		final String procId = currentProcId();
		final DeclarationInformation declInfo = idExpr.getDeclarationInformation();
		final VarMapKey keyWithOld = new VarMapKey(id, declInfo, procId);
		if (!mVarMap.containsKey(keyWithOld)) {
			VarMapValue value = null;
			if (declInfo.getStorageClass() == StorageClass.GLOBAL) {
				// Create mapping
				final DeclarationInformation newDeclInfo = new DeclarationInformation(StorageClass.LOCAL, mEntryProcId);
				final String newId = mVarIdManager.makeAndAddUniqueId(procId + "_old", id);
				value = new VarMapValue(newId, newDeclInfo);
				// Declare as local variable
				final Declaration origVarDecl = mGlobalScopeManager.getVarDeclaration(id);
				final VarList origVarList = mGlobalScopeManager.getVarListFromDeclaration(id);
				final Attribute[] newAttributes = processAttributes(origVarDecl.getAttributes());
				final ASTType type = origVarList.getType();
				// TODO Are the used ILocations intuitive?
				final VarList[] newVarLists = { new VarList(origVarList.getLocation(), new String[] { newId }, type) };
				mInlinedVars.add(new VariableDeclaration(origVarDecl.getLocation(), newAttributes, newVarLists));
			} else {
				final VarMapKey keyWithoutOld = new VarMapKey(id, declInfo);
				value = mVarMap.get(keyWithoutOld);
			}
			mVarMap.put(keyWithOld, value);
		}
	}

	/**
	 * Updates {@link #mInlinedOldVarStack} for IdentifierExpressions from inside an old() expressions. If it is a
	 * global variable, it is added the the collection on top of the stack.
	 *
	 * @param idExpr
	 *            unprocessed IdentifierExpressions from inside an old() expression.
	 */
	private void updateInlinedOldVarStack(final IdentifierExpression idExpr) {
		if (idExpr.getDeclarationInformation().getStorageClass() == StorageClass.GLOBAL) {
			final Set<IdExprWrapper> inlinedOldVars = mInlinedOldVarStack.peek();
			inlinedOldVars.add(new IdExprWrapper(idExpr));
		}
	}

	/**
	 * Generates new unique identifiers for variables and updates the map. This method is only for VarLists that are
	 * part of a procedure (no global variables for instance).
	 *
	 * @param varLists
	 *            Variables to be processed (must be part of a procedure).
	 * @param storageClass
	 *            Original StorageClass of the variables.
	 * @return List of VarLists, with new names and the same types. Use this to inline the processed variables as local
	 *         variables.
	 */
	private List<VarList> mapVariables(final VarList[] varLists, final StorageClass storageClass) {
		final boolean inEntryProcedure = inEntryProcedure();
		final String originalProcId = currentProcId();
		final boolean isQuantified = (storageClass == StorageClass.QUANTIFIED);
		final String oldDeclInfoProcId = isQuantified ? null : originalProcId;
		final DeclarationInformation oldDeclInfo = new DeclarationInformation(storageClass, oldDeclInfoProcId);
		DeclarationInformation newDeclInfo;
		if (inEntryProcedure) {
			newDeclInfo = oldDeclInfo;
		} else {
			final StorageClass newStorageClass = isQuantified ? StorageClass.QUANTIFIED : StorageClass.LOCAL;
			final String newDeclInfoProcId = isQuantified ? null : mEntryProcId;
			newDeclInfo = new DeclarationInformation(newStorageClass, newDeclInfoProcId);
		}
		final List<VarList> newVarLists = new ArrayList<>();
		for (final VarList varList : varLists) {
			final List<String> newVarIds = new ArrayList<>();
			for (final String varId : varList.getIdentifiers()) {
				String newVarId;
				if (inEntryProcedure) {
					newVarId = mVarIdManager.makeAndAddUniqueId(varId);
				} else {
					// DeclarationInformations of quantified vars contain no procedure, hence the prefix doesn't too.
					final String prefix = isQuantified ? "quantified" : originalProcId;
					newVarId = mVarIdManager.makeAndAddUniqueId(prefix, varId);
					newVarIds.add(newVarId);
				}
				final VarMapKey key = new VarMapKey(varId, oldDeclInfo);
				final VarMapValue value = new VarMapValue(newVarId, newDeclInfo);
				// quantified vars with the same id could be already mapped -- don't change the mapping for them!
				if (!mVarMap.containsKey(key)) {
					mVarMap.put(key, value);
				} else if (!isQuantified) {
					throw new AssertionError("A variable wasn't mapped properly: " + key);
				}
			}
			final String[] newVarIdsArray = newVarIds.toArray(new String[newVarIds.size()]);
			final Expression whereClause = varList.getWhereClause();
			final Expression newWhereClause = whereClause != null ? processExpression(whereClause) : null;
			final VarList newVarList =
					new VarList(varList.getLocation(), newVarIdsArray, varList.getType(), newWhereClause);
			ModelUtils.copyAnnotations(varList, newVarList);
			newVarLists.add(newVarList);
		}
		return newVarLists;
	}

	private Statement[] flattenStatementsArray(final Statement[] stats) throws CancelToolchainException {
		final List<Statement> flatStats = flattenStatements(stats);
		return flatStats.toArray(new Statement[flatStats.size()]);
	}

	private List<Statement> flattenStatements(final Statement[] stats) throws CancelToolchainException {
		final List<Statement> newStats = new ArrayList<>();
		for (final Statement stat : stats) {
			newStats.addAll(flattenStatement(stat));
		}
		return newStats;
	}

	private Deque<CallStatement> createUpdatedCallStack(final CallStatement newestCall) {
		final Deque<CallStatement> updatedCallStack = new ArrayDeque<>(mCallStackStack.peek());
		updatedCallStack.push(newestCall);
		return updatedCallStack;
	}

	private List<Statement> flattenStatement(final Statement stat) throws CancelToolchainException {
		checkTimeout();
		Statement newStat = null;
		if (stat instanceof CallStatement) {
			final CallStatement call = (CallStatement) stat;
			final int edgeIndex = getAndUpdateEdgeIndex();
			final CallGraphNode callerNode = mProcedureStack.peek();
			final CallGraphNode calleeNode = callerNode.getOutgoingNodes().get(edgeIndex);
			final CallGraphEdgeLabel edgeLabel = callerNode.getOutgoingEdgeLabels().get(edgeIndex);
			assert call.getMethodName().equals(calleeNode.getId())
					&& call.getMethodName().equals(edgeLabel.getCalleeProcedureId());
			if (edgeLabel.getInlineFlag()) {
				final VariableLHS[] processedCallLHSs = processVariableLHSs(call.getLhs());
				mCallStackStack.push(createUpdatedCallStack(call));
				mProcedureStack.push(calleeNode);
				mEdgeIndexStack.push(0);
				if (incrementCallCounter(calleeNode.getId()) <= 0) {
					mapVariablesOfCurrentProcedure();
				}
				final List<Statement> inlinedCall = inlineCall(call, processedCallLHSs, calleeNode);
				mEdgeIndexStack.pop();
				mProcedureStack.pop();
				mCallStackStack.pop();
				if (call.getPayload().hasAnnotation()) {
					mLogger.warn("Discarded annotation of " + call + ": "
							+ getClassString(call.getPayload().getAnnotations()));
				}
				mInlinerStatistic.incrementCallsInlined();
				return inlinedCall;
			}
		} else if (stat instanceof IfStatement) {
			final IfStatement ifStat = (IfStatement) stat;
			final Expression newCond = processExpression(ifStat.getCondition());
			final Statement[] newThens = flattenStatementsArray(ifStat.getThenPart());
			final Statement[] newElses = flattenStatementsArray(ifStat.getElsePart());
			newStat = new IfStatement(ifStat.getLocation(), newCond, newThens, newElses);
		} else if (stat instanceof WhileStatement) {
			final WhileStatement whileStat = (WhileStatement) stat;
			final Expression newCond = processExpression(whileStat.getCondition());
			final LoopInvariantSpecification[] newInvs = processLoopSpecifications(whileStat.getInvariants());
			final Statement[] newBody = flattenStatementsArray(whileStat.getBody());
			newStat = new WhileStatement(whileStat.getLocation(), newCond, newInvs, newBody);
		}
		if (newStat == null) {
			newStat = processStatement(stat); // also adds backtranslation
		} else {
			ModelUtils.copyAnnotations(stat, newStat);
			addBacktranslation(newStat, stat);
		}
		mInlinerStatistic.incrementStatementsFlattened();
		return Collections.singletonList(newStat);
	}

	private static String getClassString(final Map<String, IAnnotations> annotations) {
		if (annotations == null) {
			return "NULL";
		}
		return annotations.entrySet().stream()
				.map(a -> a.getKey() + " -> " + (a.getValue() == null ? "NULL" : a.getValue().getClass()))
				.collect(Collectors.joining(", "));
	}

	/**
	 * Creates an inline version of a call.
	 *
	 * @code{call forall} statements aren't supported.
	 *
	 * @param call
	 *            Normal, unprocessed CallStatement which should be inlined.
	 * @param processedCallLHS
	 *            Processed LHS of the CallStatement. The LHS instances from the array need to be unique for each call
	 *            of this method.
	 * @param calleeNode
	 *            CallGrapNode of the called procedure
	 * @return Inline version of the call.
	 *
	 * @throws CancelToolchainException
	 *             The program contained constructs which couldn't be inlined (e.g. recursion).
	 */
	private List<Statement> inlineCall(final CallStatement call, final VariableLHS[] processedCallLHS,
			final CallGraphNode calleeNode) throws CancelToolchainException {

		mInlinedOldVarStack.push(new HashSet<IdExprWrapper>());

		final String procId = calleeNode.getId();
		assert procId.equals(call.getMethodName());
		if (stackContainsDuplicates()) {
			throw new InliningUnsupportedException("Recursive call: " + call, call.getLocation());
		} else if (call.isForall()) {
			throw new InliningUnsupportedException("Call forall: " + call, call.getLocation());
		}

		// --------- inline specifications ---------
		final Procedure procWithSpec = calleeNode.getProcedureWithSpecification();
		final Specification[] specs = procWithSpec.getSpecification();
		final List<Statement> assertRequires = new ArrayList<>();
		final List<Statement> assumeRequires = new ArrayList<>();
		final List<Statement> assertEnsures = new ArrayList<>();
		final List<Statement> assumeEnsures = new ArrayList<>();
		final List<ModifiesSpecification> unprocessedModSpecs = new ArrayList<>();
		for (final Specification spec : specs) {
			final Specification processedSpec = processSpecification(spec);
			final ILocation loc = processedSpec.getLocation();
			final boolean isFree = processedSpec.isFree();
			if (processedSpec instanceof RequiresSpecification) {
				final Expression processedFormula = ((RequiresSpecification) processedSpec).getFormula();
				if (isFree) {
					throw new InliningUnsupportedException("Free ensures: " + call, call.getLocation());
				}
				// assert PRE
				final AssertStatement assertStat = new AssertStatement(loc, processedFormula);
				ModelUtils.copyAnnotations(processedSpec, assertStat);
				addBacktranslation(assertStat, spec);
				assertRequires.add(assertStat);
				// assume PRE
				final AssumeStatement assumeStat = new AssumeStatement(loc, processedFormula);
				ModelUtils.copyAnnotations(processedSpec, assumeStat);
				addBacktranslation(assumeStat, null); // "assert PRE" is always there and translates to the spec
				assumeRequires.add(assumeStat);
			} else if (processedSpec instanceof EnsuresSpecification) {
				final Expression formula = ((EnsuresSpecification) processedSpec).getFormula();
				if (!isFree && calleeNode.isImplemented()) {
					// assert POST
					final AssertStatement assertStat = new AssertStatement(loc, formula);
					ModelUtils.copyAnnotations(processedSpec, assertStat);
					addBacktranslation(assertStat, null); // "assume POST" is always there and translates to the spec
					assertEnsures.add(assertStat);
				}
				// assume POST
				final AssumeStatement assumeStat = new AssumeStatement(loc, formula);
				ModelUtils.copyAnnotations(processedSpec, assumeStat);
				addBacktranslation(assumeStat, spec);
				assumeEnsures.add(assumeStat);
			} else if (processedSpec instanceof ModifiesSpecification) {
				unprocessedModSpecs.add((ModifiesSpecification) processedSpec);
			}
		}

		// --------- inline body (or havoc, if unimplemented) ---------
		final ILocation callLocation = call.getLocation();
		Procedure proc;
		final List<Statement> inlinedBody = new ArrayList<>();

		// havoc out-parameters (they are reused for different calls)
		final VarList[] outParams = procWithSpec.getOutParams();
		if (outParams.length > 0) {
			final DeclarationInformation declInfo = new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, procId);
			final List<VariableLHS> outParamLHSs = varListsToVarLHSs(outParams, declInfo);
			if (!outParamLHSs.isEmpty()) {
				final VariableLHS[] outParamLHSsArray = outParamLHSs.toArray(new VariableLHS[outParamLHSs.size()]);
				final Statement havocOutParams = processStatement(new HavocStatement(callLocation, outParamLHSsArray));
				addBacktranslation(havocOutParams, null);
				inlinedBody.add(havocOutParams);
			}
		}

		if (calleeNode.isImplemented()) {
			proc = calleeNode.getProcedureWithBody();
			final Body body = proc.getBody();
			final Statement[] block = body.getBlock();
			mapLabels(block);
			mapReturnLabel();

			// havoc local variables (they are reused for different calls)
			final List<VariableLHS> localVarLHS = new ArrayList<>();
			final DeclarationInformation localDeclInfo = new DeclarationInformation(StorageClass.LOCAL, procId);
			for (final VariableDeclaration varDecl : body.getLocalVars()) {
				localVarLHS.addAll(varListsToVarLHSs(varDecl.getVariables(), localDeclInfo));
			}
			if (!localVarLHS.isEmpty()) {
				final VariableLHS[] localVarLHSArray = localVarLHS.toArray(new VariableLHS[localVarLHS.size()]);
				final Statement havocLocalVars = processStatement(new HavocStatement(callLocation, localVarLHSArray));
				addBacktranslation(havocLocalVars, null);
				inlinedBody.add(havocLocalVars);
			}

			// inline body
			inlinedBody.addAll(flattenStatements(block));

			// insert end label (ReturnStatements are inlined as jumps to this label)
			final Label returnLabel = new Label(proc.getLocation(), getCurrentReturnLabelId());
			addBacktranslation(returnLabel, null);
			inlinedBody.add(returnLabel);

		} else { // unimplemented procedure

			// havoc global variables from modifies specifications
			proc = calleeNode.getProcedureWithSpecification();
			for (final ModifiesSpecification modSpec : unprocessedModSpecs) {
				final ModifiesSpecification processedModSpec = (ModifiesSpecification) processSpecification(modSpec);
				final VariableLHS[] processedModVars = processedModSpec.getIdentifiers();
				if (processedModVars.length > 0) {
					final Statement havocModifiedVars =
							new HavocStatement(processedModSpec.getLocation(), processedModVars);
					ModelUtils.copyAnnotations(processedModSpec, havocModifiedVars);
					addBacktranslation(havocModifiedVars, modSpec); // TODO remove from backtranslated trace?
					inlinedBody.add(havocModifiedVars);
				}
			}
		}
		final ILocation procLocation = proc.getLocation();
		final boolean procHasSpec = (proc.getSpecification() != null);

		// --------- assign call arguments to in-parameters ---------
		final List<Statement> writeToInParams = new ArrayList<>();
		if (proc.getInParams().length > 0) {
			final Expression[] inVarRHSs = call.getArguments();
			final VariableLHS[] inVarLHSs = new VariableLHS[inVarRHSs.length];
			final VarListIterator inParamsIterator = new VarListIterator(proc.getInParams());
			final DeclarationInformation inParamDeclInfo = new DeclarationInformation(
					procHasSpec ? StorageClass.PROC_FUNC_INPARAM : StorageClass.IMPLEMENTATION_INPARAM,
					calleeNode.getId());
			for (int i = 0; i < inVarRHSs.length; ++i) {
				inParamsIterator.next();
				final IBoogieType inParamType = inParamsIterator.currentVarList(0).getType().getBoogieType();
				final String inParamId = inParamsIterator.currentId(0);
				inVarLHSs[i] = new VariableLHS(proc.getLocation(), inParamType, inParamId, inParamDeclInfo);
			}
			final Statement assignStat = processStatement(new AssignmentStatement(callLocation, inVarLHSs, inVarRHSs));
			addBacktranslation(assignStat, null);
			writeToInParams.add(assignStat);
		}

		// --------- assign out-parameters to target variables from call statement ---------
		final List<Statement> writeFromOutParams = new ArrayList<>();
		if (proc.getOutParams().length > 0) {
			final Expression[] processedOutParamRHS = new Expression[processedCallLHS.length];
			final VarListIterator outParamsIterator = new VarListIterator(proc.getOutParams());
			final DeclarationInformation outParamDeclInfo = new DeclarationInformation(
					procHasSpec ? StorageClass.PROC_FUNC_OUTPARAM : StorageClass.IMPLEMENTATION_OUTPARAM,
					calleeNode.getId());
			for (int i = 0; i < processedCallLHS.length; ++i) {
				outParamsIterator.next();
				final IBoogieType outParamType = outParamsIterator.currentVarList(0).getType().getBoogieType();
				final String outParamId = outParamsIterator.currentId(0);
				processedOutParamRHS[i] = processExpression(
						new IdentifierExpression(procLocation, outParamType, outParamId, outParamDeclInfo));
			}
			final Statement assignStat = new AssignmentStatement(callLocation, processedCallLHS, processedOutParamRHS);
			addBacktranslation(assignStat, null);
			writeFromOutParams.add(assignStat);
		}

		// --------- keep old state of global vars, which appear inside old() expressions ---------
		final Set<IdExprWrapper> oldVars = mInlinedOldVarStack.pop();
		final Iterator<IdExprWrapper> oldVarsIterator = oldVars.iterator();
		final DeclarationInformation declInfoGlobal = new DeclarationInformation(StorageClass.GLOBAL, null);
		final VariableLHS[] oldVarLHS = new VariableLHS[oldVars.size()];
		final Expression[] oldVarRHS = new Expression[oldVars.size()];
		for (int i = 0; oldVarsIterator.hasNext(); ++i) {
			final IdentifierExpression idExpr = oldVarsIterator.next().getIdExpr();
			final String id = idExpr.getIdentifier();
			final IBoogieType type = idExpr.getType();
			final VarMapValue mapping = mVarMap.get(new VarMapKey(id, declInfoGlobal, proc.getIdentifier()));
			oldVarLHS[i] = new VariableLHS(callLocation, type, mapping.getVarId(), mapping.getDeclInfo());
			oldVarRHS[i] = new IdentifierExpression(callLocation, type, id, declInfoGlobal);
		}

		// --------- build the block to be inserted instead of the call ---------
		final List<Statement> inlineBlock = new ArrayList<>();
		if (oldVarLHS.length > 0) {
			// safe global variables
			final Statement assignStat = new AssignmentStatement(callLocation, oldVarLHS, oldVarRHS);
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

	private List<VariableLHS> varListsToVarLHSs(final VarList[] varLists, final DeclarationInformation declInfo) {
		final List<VariableLHS> varLHSs = new ArrayList<>(3 * varLists.length);
		for (final VarList varList : varLists) {
			final IBoogieType type = varList.getType().getBoogieType();
			final ILocation location = varList.getLocation();
			for (final String id : varList.getIdentifiers()) {
				varLHSs.add(new VariableLHS(location, type, id, declInfo));
			}
		}
		return varLHSs;
	}

	@Override
	protected Statement processStatement(final Statement stat) {
		Statement newStat = null;
		if (stat instanceof Label) {
			final Label label = (Label) stat;
			newStat = new Label(label.getLocation(), getNewLabelId(label.getName()));
		} else if (stat instanceof GotoStatement) {
			final GotoStatement gotoStat = (GotoStatement) stat;
			final String[] labelIds = gotoStat.getLabels();
			final String[] newLabelIds = new String[labelIds.length];
			for (int i = 0; i < labelIds.length; ++i) {
				newLabelIds[i] = getNewLabelId(labelIds[i]);
			}
			newStat = new GotoStatement(gotoStat.getLocation(), newLabelIds);
		} else if (stat instanceof BreakStatement) {
			final BreakStatement breakStat = (BreakStatement) stat;
			final String label = breakStat.getLabel();
			if (label != null) {
				newStat = new BreakStatement(breakStat.getLocation(), getNewLabelId(label));
			}
		} else if (stat instanceof ReturnStatement && !inEntryProcedure()) {
			newStat = new GotoStatement(stat.getLocation(), new String[] { getCurrentReturnLabelId() });
		}
		if (newStat == null) {
			newStat = super.processStatement(stat);
		} else {
			ModelUtils.copyAnnotations(stat, newStat);
		}
		addBacktranslation(newStat, stat);
		return newStat;
	}

	@Override
	protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
		LeftHandSide newLhs = null;
		if (lhs instanceof VariableLHS) {
			final VariableLHS varLhs = (VariableLHS) lhs;
			final DeclarationInformation declInfo = varLhs.getDeclarationInformation();
			final VarMapValue mapping = mVarMap.get(new VarMapKey(varLhs.getIdentifier(), declInfo, inOldExprOfProc()));
			final String newId = mapping.getVarId();
			final DeclarationInformation newDeclInfo = mapping.getDeclInfo();
			newLhs = new VariableLHS(varLhs.getLocation(), varLhs.getType(), newId, newDeclInfo);
		} else if (lhs instanceof StructLHS) {
			final StructLHS structLhs = (StructLHS) lhs;
			final LeftHandSide newStructStruct = processLeftHandSide(structLhs.getStruct());
			newLhs = new StructLHS(structLhs.getLocation(), newStructStruct, structLhs.getField());
		} else if (lhs instanceof ArrayLHS) {
			final ArrayLHS arrayLhs = (ArrayLHS) lhs;
			final LeftHandSide newArray = processLeftHandSide(arrayLhs.getArray());
			final Expression[] newIndices = processExpressions(arrayLhs.getIndices());
			newLhs = new ArrayLHS(lhs.getLocation(), arrayLhs.getType(), newArray, newIndices);
		} else {
			throw new UnsupportedOperationException("Cannot process unknown LHS: " + lhs.getClass().getName());
		}
		ModelUtils.copyAnnotations(lhs, newLhs);
		return newLhs;
	}

	private String getNewLabelId(final String oldLabelId) {
		final String procId = currentProcId();
		final String newName = mLabelMap.get(new LabelMapKey(oldLabelId, procId, getCallCounter(procId)));
		assert newName != null : "Missing mapping for Label: " + oldLabelId;
		return newName;
	}

	private void mapReturnLabel() {
		final String procId = currentProcId();
		final String returnLabelId = mLabelIdManager.makeAndAddUniqueId(procId, "returnLabel");
		mLabelMap.put(createCurrentReturnLabelKey(), returnLabelId);
	}

	private String getCurrentReturnLabelId() {
		return mLabelMap.get(createCurrentReturnLabelKey());
	}

	private LabelMapKey createCurrentReturnLabelKey() {
		final String procId = currentProcId();
		// we can use the call counter, because recursion is forbidden
		return new LabelMapKey(null, procId, getCallCounter(procId));
	}

	private void mapLabels(final Statement[] stats) {
		for (final Statement stat : stats) {
			mapLabels(stat);
		}
	}

	private void mapLabels(final Statement stat) {
		if (stat instanceof WhileStatement) {
			mapLabels(((WhileStatement) stat).getBody());
		} else if (stat instanceof IfStatement) {
			final IfStatement ifStat = (IfStatement) stat;
			mapLabels(ifStat.getThenPart());
			mapLabels(ifStat.getElsePart());
		} else if (stat instanceof Label) {
			final String procId = currentProcId();
			final String labelId = ((Label) stat).getName();
			String newLabelId;
			if (inEntryProcedure()) {
				newLabelId = mLabelIdManager.addId(labelId);
			} else {
				newLabelId = mLabelIdManager.makeAndAddUniqueId(procId, labelId);
			}
			final LabelMapKey key = new LabelMapKey(labelId, procId, getCallCounter(procId));
			mLabelMap.put(key, newLabelId);
		}
	}

	@Override
	protected Expression processExpression(final Expression expr) {
		Expression newExpr = null;
		if (expr instanceof IdentifierExpression) {
			final IdentifierExpression idExpr = (IdentifierExpression) expr;
			final String id = idExpr.getIdentifier();
			final DeclarationInformation declInfo = idExpr.getDeclarationInformation();
			final String inOldExprOfProc = inOldExprOfProc();
			if (inOldExprOfProc != null) {
				mapVariableInInlinedOldExpr(idExpr); // includes check to avoid mapping of already mapped values
				updateInlinedOldVarStack(idExpr);
			}
			final VarMapValue mapping = mVarMap.get(new VarMapKey(id, declInfo, inOldExprOfProc));
			final String newId = mapping.getVarId();
			final DeclarationInformation newDeclInfo = mapping.getDeclInfo();
			newExpr = new IdentifierExpression(idExpr.getLocation(), idExpr.getType(), newId, newDeclInfo);
		} else if (expr instanceof QuantifierExpression) {
			final QuantifierExpression quantExpr = (QuantifierExpression) expr;
			final ILocation location = quantExpr.getLocation();
			final IBoogieType type = quantExpr.getType();
			final VarList[] params = quantExpr.getParameters();
			final Attribute[] attrs = quantExpr.getAttributes();
			final Expression formula = quantExpr.getSubformula();

			mapVariables(quantExpr.getParameters(), StorageClass.QUANTIFIED);
			// quantified vars don't have to be added to the inlined local variables,
			// because they don't have to be defined as local variables

			final VarList[] newParams =
					applyMappingToVarList(params, new DeclarationInformation(StorageClass.QUANTIFIED, null));
			final Attribute[] newAttrs = processAttributes(attrs);
			final Expression newFormula = processExpression(formula);
			newExpr = new QuantifierExpression(location, type, quantExpr.isUniversal(), quantExpr.getTypeParams(),
					newParams, newAttrs, newFormula);
		} else if (expr instanceof UnaryExpression
				&& ((UnaryExpression) expr).getOperator() == UnaryExpression.Operator.OLD && !inEntryProcedure()) {
			final UnaryExpression unaryExpr = (UnaryExpression) expr;
			mInlinedOldExprStack.push(unaryExpr);
			newExpr = processExpression(unaryExpr.getExpr());
			mInlinedOldExprStack.pop();
		}
		if (newExpr == null) {
			newExpr = super.processExpression(expr);
		} else {
			ModelUtils.copyAnnotations(expr, newExpr);
		}
		addBacktranslation(newExpr, expr);
		return newExpr;
	}

	/**
	 * Applies the mapping to a VarList. Intended for mapping of procedure parameters. This method should be used in
	 * place of {@linkplain #processVarLists(VarList[])}.
	 *
	 * @param vls
	 *            Original VarLists.
	 * @param declInfo
	 *            Original DeclarationInformation of the variables from the VarLists.
	 * @return Mapped VarLists (note: the DeclarationInformation might have changed too).
	 */
	protected VarList[] applyMappingToVarList(final VarList vls[], final DeclarationInformation declInfo) {
		final VarList[] newVls = new VarList[vls.length];
		boolean changed = false;
		for (int i = 0; i < vls.length; ++i) {
			final VarList vl = vls[i];
			final VarList newVl = applyMappingToVarList(vl, declInfo);
			if (newVl != vl) {
				changed = true;
			}
			newVls[i] = newVl;
		}
		return changed ? newVls : vls;
	}

	/**
	 * Applies the mapping to a VarList. Intended for mapping of procedure parameters. This method should be used in
	 * place of {@linkplain #processVarList(VarList)}.
	 *
	 * @param vl
	 *            Original VarList.
	 * @param declInfo
	 *            Original DeclarationInformation of the variables from the VarList.
	 * @return Mapped VarList (note: the DeclarationInformation might have changed too).
	 */
	private VarList applyMappingToVarList(final VarList vl, final DeclarationInformation declInfo) {
		final Expression where = vl.getWhereClause();
		final Expression newWhere = where != null ? processExpression(where) : null;
		final String[] ids = vl.getIdentifiers();
		final String[] newIds = applyMappingToVarIds(ids, declInfo);
		if (newWhere != where || ids != newIds) {
			final VarList newVl = new VarList(vl.getLocation(), newIds, vl.getType(), newWhere);
			ModelUtils.copyAnnotations(vl, newVl);
			return newVl;
		}
		return vl;
	}

	/**
	 * Applies the mapping to identifiers of variables.
	 *
	 * @param ids
	 *            Original identifiers of variables.
	 * @param declInfo
	 *            Original DeclarationInformation of the variables.
	 * @return Mapped Identifiers (note: the DeclarationInformation might have changed too).
	 */
	private String[] applyMappingToVarIds(final String[] ids, final DeclarationInformation declInfo) {
		final String[] newIds = new String[ids.length];
		boolean changed = false;
		for (int i = 0; i < ids.length; ++i) {
			final String id = ids[i];
			final String newId = mVarMap.get(new VarMapKey(id, declInfo, inOldExprOfProc())).getVarId();
			if (!newId.equals(id)) {
				changed = true;
			}
			newIds[i] = newId;
		}
		return changed ? newIds : ids;
	}

	/**
	 * Disabled due to parameters restriction of super class. We need more parameters for a correct mapping of the
	 * variables.
	 *
	 * @see #applyMappingToVarList(VarList, DeclarationInformation)
	 * @see #applyMappingToVarList(VarList[], DeclarationInformation)
	 */
	@Deprecated
	@Override
	protected VarList processVarList(final VarList varList) {
		throw new UnsupportedOperationException("Use \"applyMappingToVarList(...)\" instead.");
	}

	/**
	 * Creates the last argument for the constructor of VarMapKey.
	 *
	 * @return Current procedure identifier, if processing takes place inside an inlined old() expression, {@code null}
	 *         otherwise.
	 */
	private String inOldExprOfProc() {
		if (inInlinedOldExpr()) {
			return currentProcId();
		} else {
			return null;
		}
	}

	private void checkTimeout() {
		if (!mProgressMonitorService.continueProcessing()) {
			final String msg = "inlining (statistic: " + mInlinerStatistic + ")";
			throw new ToolchainCanceledException(this.getClass(), msg);
		}
	}
}
