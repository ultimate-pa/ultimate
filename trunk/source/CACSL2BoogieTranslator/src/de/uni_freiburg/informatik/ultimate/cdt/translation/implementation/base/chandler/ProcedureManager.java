/*
 * Copyright (C) 2013-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.BoogieGlobalLhsFinder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.HandlerHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.StandardFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UndeclaredFunctionException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.LinkedHashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.DefaultSccComputation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * Manages the Boogie procedures of the translated program.
 * <p>
 * Boogie procedures are inserted into the translated program from several
 * sources:
 * <li>translations of C functions ({@link CHandler}, {@link FunctionHandler})
 * <li>helper procedures from the memory model ({@link MemoryHandler})
 * <li>when we provide a Boogie model for a standard C function
 * ({@link StandardFunctionHandler})
 * <li>Ultimate.start and Ultimate.init ({@link PostProcessor})
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ProcedureManager {

	private final Set<BoogieProcedureInfo> mMethodsCalledBeforeDeclared;

	private final Map<String, BoogieProcedureInfo> mProcedureNameToProcedureInfo;
	private final LinkedHashRelation<BoogieProcedureInfo, BoogieProcedureInfo> mInverseCallGraph;

	private BoogieProcedureInfo mCurrentProcedureInfo;

	public ProcedureManager(final HandlerHandler handlerHandler) {
		handlerHandler.setProcedureManager(this);

		mMethodsCalledBeforeDeclared = new LinkedHashSet<>();
		mProcedureNameToProcedureInfo = new LinkedHashMap<>();
		mInverseCallGraph = new LinkedHashRelation<>();
	}

	void beginProcedureScope(final Dispatcher main, final BoogieProcedureInfo currentProcInfo) {
		mCurrentProcedureInfo = currentProcInfo;
		main.mCHandler.beginScope();
	}

	void endProcedureScope(final Dispatcher main) {
		mCurrentProcedureInfo = null;
		main.mCHandler.endScope();
	}

	/**
	 * Announce the use of a procedure to the FunctionHandler
	 *
	 * @param methodName
	 */
	public void registerProcedure(final String methodName) {
		getOrConstructProcedureInfo(methodName);
	}

	public void registerProcedureDeclaration(final String procName, final Procedure declaration) {
		final BoogieProcedureInfo procInfo = getOrConstructProcedureInfo(procName);
		if (procInfo.hasDeclaration()) {
			throw new IllegalStateException("procedure already has a declaration, this is unexpected");
		}
		procInfo.setDeclaration(declaration);
	}

	BoogieProcedureInfo getOrConstructProcedureInfo(final String methodName) {

		BoogieProcedureInfo result = mProcedureNameToProcedureInfo.get(methodName);
		if (result == null) {
			result = new BoogieProcedureInfo(methodName);
			mProcedureNameToProcedureInfo.put(methodName, result);
		}

		return result;
	}

	/**
	 * expects that we have already constructed a ProcedureInfo for the given name
	 *
	 * @param procName
	 * @return
	 */
	BoogieProcedureInfo getProcedureInfo(final String procName) {
		final BoogieProcedureInfo result = mProcedureNameToProcedureInfo.get(procName);
		if (result == null) {
			throw new IllegalArgumentException("a procedure of the given name is not yet known " + procName);
		}
		return result;
	}

	/**
	 * This method is expected to be called from CHandler.visit(..TranslationUnit)
	 * after all procedures have been registered in the FunctionHandler.
	 * <p>
	 * Returns declarations for all procedures that will appear in the translated
	 * program. Ensures that the modifies clauses of all procedures are transitive
	 * with respect to the call graph.
	 * <p>
	 * Special case regarding memory models: if one memory-array is included, all
	 * active memory arrays have to be included (f.i. we have procedure modifies
	 * memory_int, and memoryHandler.isFloatMMArray == true, and
	 * memoryHandler.isIntMMArray == true, memoryHandler.isPointerMMArray == false,
	 * then we have to add memory_real to the modifies clause of procedure
	 *
	 * @param main
	 *            a reference to the main dispatcher.
	 * @return procedure declarations
	 */
	public List<Declaration> computeFinalProcedureDeclarations(final Dispatcher main,
			final MemoryHandler memoryHandler) {
		final BoogieProcedureInfo notDeclaredProcedure = isEveryCalledProcedureDeclared();
		if (notDeclaredProcedure != null) {
			throw new UndeclaredFunctionException(null, "a function that is called in the program "
					+ "is not declared in the program: " + notDeclaredProcedure.getProcedureName());
		}

		/**
		 * The base graph for the computation of strongly connected components (SCCs) is
		 * the inverse call graph. I.e., in the sense of this graph, the successors of a
		 * procedure are its callers.
		 */
		final ISuccessorProvider<BoogieProcedureInfo> successorProvider = new ISuccessorProvider<BoogieProcedureInfo>() {
			@Override
			public Iterator<BoogieProcedureInfo> getSuccessors(final BoogieProcedureInfo node) {
				return mInverseCallGraph.getImage(node).iterator();
			}
		};

		final int numberOfAllNodes = mProcedureNameToProcedureInfo.size();
		final Set<BoogieProcedureInfo> startNodes = new HashSet<>(mProcedureNameToProcedureInfo.values());
		final DefaultSccComputation<BoogieProcedureInfo> dssc = new DefaultSccComputation<>(main.getLogger(),
				successorProvider, numberOfAllNodes, startNodes);

		/*
		 * Initialize the modified globals for each SCC with the union of each method's
		 * modified globals. (within an SCC all procedure may call all others (possibly
		 * transitively) thus all must have the same modifies clause contents)
		 */
		final LinkedHashRelation<StronglyConnectedComponent<BoogieProcedureInfo>, VariableLHS> sccToModifiedGlobals = new LinkedHashRelation<>();
		for (final StronglyConnectedComponent<BoogieProcedureInfo> scc : dssc.getSCCs()) {
			for (final BoogieProcedureInfo procInfo : scc.getNodes()) {
				for (final VariableLHS modGlobal : procInfo.getModifiedGlobals()) {
					sccToModifiedGlobals.addPair(scc, modGlobal);
				}
			}
		}

		/*
		 * update the modified globals for the sccs according to the edges in the call
		 * graph that connect different SCCs
		 *
		 * algorithmic idea: start with the leafs of the graph and propagate all
		 * modified globals back along call edges. The frontier is where we have already
		 * propagated modified globals.
		 *
		 */
		final Deque<StronglyConnectedComponent<BoogieProcedureInfo>> frontier = new ArrayDeque<>();
		// frontier.addAll(dssc.getLeafComponents());
		frontier.addAll(dssc.getRootComponents());
		while (!frontier.isEmpty()) {
			final StronglyConnectedComponent<BoogieProcedureInfo> currentScc = frontier.pollFirst();

			/*
			 * Note that we have chosen the ISuccessorProvider for the SccComputation such
			 * that the caller is the successor of the callee. (i.e., the successor relation
			 * is the inverse of the call graph)
			 */
			final Set<VariableLHS> currentSccModGlobals = sccToModifiedGlobals.getImage(currentScc);
			final Iterator<StronglyConnectedComponent<BoogieProcedureInfo>> callers = dssc
					.getComponentsSuccessorsProvider().getSuccessors(currentScc);
			while (callers.hasNext()) {
				final StronglyConnectedComponent<BoogieProcedureInfo> caller = callers.next();
				frontier.add(caller);

				for (final VariableLHS currentSccModGlobal : currentSccModGlobals) {
					sccToModifiedGlobals.addPair(caller, currentSccModGlobal);
				}
			}
		}

		// update the modifies clauses!
		final ArrayList<Declaration> updatedDeclarations = new ArrayList<>();
		for (final BoogieProcedureInfo procInfo : mProcedureNameToProcedureInfo.values()) {
			final Procedure oldProcDecl = procInfo.getDeclaration();

			final String procedureName = procInfo.getProcedureName();
			final Specification[] oldSpec = oldProcDecl.getSpecification();
			final CACSLLocation loc = (CACSLLocation) oldProcDecl.getLocation();

			final Specification[] newSpec;
			if (procInfo.isModifiedGlobalsIsUsedDefined()) {
				// modifies clause is user defined --> leave the specification as is
				newSpec = oldSpec;
			} else {
				// // case: !procInfo.isModifiedGlobalsIsUsedDefined()
				final Set<VariableLHS> currModClause = sccToModifiedGlobals
						.getImage(dssc.getNodeToComponents().get(procInfo));
				assert currModClause != null : "No modifies clause proc " + procedureName;

				// final Set<VariableLHS> currModClauseDuplicatesFiltered =
				// filterDuplicateVariableLHSs(currModClause);

				procInfo.addModifiedGlobals(currModClause);

				newSpec = Arrays.copyOf(oldSpec, oldSpec.length + 1);

				{
					/*
					 * add missing heap arrays If the procedure modifies one heap array, we add all
					 * heap arrays. This is a workaround. We cannot add all procedures immediately,
					 * because we do not know all heap arrays in advance since they are added lazily
					 * on demand.
					 *
					 */
					final Collection<HeapDataArray> heapDataArrays = memoryHandler.getMemoryModel()
							.getDataHeapArrays(memoryHandler.getRequiredMemoryModelFeatures());
					if (containsOneHeapDataArray(currModClause, heapDataArrays)) {
						for (final HeapDataArray hda : heapDataArrays) {
							// currModClause.add(hda.getVariableName());
							procInfo.addModifiedGlobal(hda.getVariableLHS());
						}
					}
				}

				final VariableLHS[] modifyList = new VariableLHS[currModClause.size()];
				{
					int i = 0;
					for (final VariableLHS modifyEntry : currModClause) {
						modifyList[i++] = modifyEntry;// new VariableLHS(loc, modifyEntry);
					}
				}
				newSpec[oldSpec.length] = constructModifiesSpecification(loc, false, modifyList);
			}

			/*
			 *
			 */
			final Specification[] newSpecWithExtraEnsuresClauses;
			if (memoryHandler.getRequiredMemoryModelFeatures().isMemoryModelInfrastructureRequired() && (main
					.getPreferences().getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_ALLOCATION_PURITY)
					|| (main.getCheckedMethod().equals(SFO.EMPTY) || main.getCheckedMethod().equals(procedureName))
							&& main.getPreferences()
									.getBoolean(CACSLPreferenceInitializer.LABEL_CHECK_MEMORY_LEAK_IN_MAIN))) {
				// add a specification to check for memory leaks

				// final Expression vIe = new IdentifierExpression(loc, SFO.VALID);
				final Expression vIe = // ExpressionFactory.constructIdentifierExpression(loc, MemoryModelDeclarations
										// SFO.VALID);
						main.mCHandler.getMemoryHandler().getValidArray(loc);

				final int nrSpec = newSpec.length;
				final Check check = new Check(Check.Spec.MEMORY_LEAK);
				final ILocation ensLoc = LocationFactory.createLocation(loc, check);
				newSpecWithExtraEnsuresClauses = Arrays.copyOf(newSpec, nrSpec + 1);
				newSpecWithExtraEnsuresClauses[nrSpec] = new EnsuresSpecification(ensLoc, false,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, vIe,
								ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, vIe)));
				check.annotate(newSpecWithExtraEnsuresClauses[nrSpec]);
				if (main.getPreferences()
						.getBoolean(CACSLPreferenceInitializer.LABEL_SVCOMP_MEMTRACK_COMPATIBILITY_MODE)) {
					new Overapprox(Collections.singletonMap("memtrack", ensLoc))
							.annotate(newSpecWithExtraEnsuresClauses[nrSpec]);
				}
			} else {
				newSpecWithExtraEnsuresClauses = newSpec;
			}
			updatedDeclarations.add(new Procedure(loc, oldProcDecl.getAttributes(), procedureName,
					oldProcDecl.getTypeParams(), oldProcDecl.getInParams(), oldProcDecl.getOutParams(),
					newSpecWithExtraEnsuresClauses, null));
		}
		return updatedDeclarations;
	}

	/**
	 * only keep variable lhss that refer to the same global variable, i.e., keep
	 * only one per identifier String.
	 *
	 * @return
	 */
	private Set<VariableLHS> filterDuplicateVariableLHSs(final Set<VariableLHS> input) {
		final Set<VariableLHS> result = new LinkedHashSet<>();
		final Set<String> seenLhsNames = new LinkedHashSet<>();
		for (final VariableLHS lhs : input) {
			if (seenLhsNames.contains(lhs.getIdentifier())) {
				continue;
			}
			result.add(lhs);
			seenLhsNames.add(lhs.getIdentifier());
		}
		return result;
	}

	private static boolean containsOneHeapDataArray(final Set<VariableLHS> modifySet,
			final Collection<HeapDataArray> heapDataArrays) {
		for (final HeapDataArray hda : heapDataArrays) {
			if (modifySet.contains(hda.getVariableLHS())) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Announces that the procedure that is currently being translated calls another
	 * procedure.
	 *
	 * @param callee
	 */
	@Deprecated
	public void registerCall(final String callee) {
		if (isGlobalScope()) {
			throw new IllegalStateException("attempting to register a call when in global scope");
		}
		// registerCall(mCurrentProcedureInfo, getProcedureInfo(callee));
		registerCall(mCurrentProcedureInfo, getOrConstructProcedureInfo(callee));
	}

	/**
	 * Announces that a procedure calls another procedure somewhere in the
	 * translated program. (for example this updates the call graph accordingly)
	 *
	 * @param caller
	 * @param callee
	 */
	@Deprecated
	public void registerCall(final String caller, final String callee) {
		registerCall(getOrConstructProcedureInfo(caller), getOrConstructProcedureInfo(callee));
	}

	void registerCall(final BoogieProcedureInfo caller, final BoogieProcedureInfo callee) {
		if (!callee.hasDeclaration()) {
			mMethodsCalledBeforeDeclared.add(callee);
		}

		mInverseCallGraph.addPair(callee, caller);
	}

	/**
	 * Checks, whether all procedures that are being called in C, were eventually
	 * declared within the C program.
	 *
	 * @return null if all called procedures were declared, otherwise the identifier
	 *         of one procedure that was called but not declared.
	 */
	private BoogieProcedureInfo isEveryCalledProcedureDeclared() {
		for (final BoogieProcedureInfo s : mMethodsCalledBeforeDeclared) {
			if (!s.hasDeclaration()) {
				return s;
			}
		}
		return null;
	}

	/**
	 * Announces the beginning of the declaration of a custom procedure. A custom
	 * procedure is a procedure that is introduced by the translation and has no
	 * direct counterpart in the translated C program. Examples are Ultimate.start,
	 * Ultimate.init, and the procedures introduces by the memory model.
	 *
	 * @param main
	 * @param loc
	 * @param procedureName
	 * @param procedureDecl
	 *            initial declaration for the procedure, should contain the
	 *            signature, may be reset later for adding specifications; modifies
	 *            specification will be generated by FunctionHandler like for all
	 *            procedures.
	 */
	void beginCustomProcedure(final Dispatcher main, final ILocation loc, final String procedureName,
			final Procedure procedureDecl) {
		// main.mCHandler.beginScope();

		final BoogieProcedureInfo procInfo = getOrConstructProcedureInfo(procedureName);
		procInfo.setDeclaration(procedureDecl);

		beginProcedureScope(main, procInfo);
		// mCurrentProcedure = new Procedure(loc, new Attribute[0], startOrInit, new
		// String[0], new VarList[0],
		// new VarList[0], new Specification[0], null);
		//
		// final ProcedureInfo procInfo = getOrConstructProcedureInfo(startOrInit);
		// procInfo.setDeclaration(mCurrentProcedure);

		// mModifiedGlobals.put(mCurrentProcedure.getIdentifier(), new
		// LinkedHashSet<String>());
		// registerProcedureDeclaration(main, loc, null, name,
		// new CFunction(new CPrimitive(CPrimitives.VOID), new CDeclaration[0], false));
		// registerProcedureDeclaration(main, loc, null, procedureName, procedureDecl);

	}

	/**
	 *
	 * @param main
	 * @param initDecl
	 *            note this must be a pure declaration, i.e., its body must be null
	 * @param procName
	 * @param calledProcedures
	 */
	void endCustomProcedure(final Dispatcher main, final String procName) {
		assert mCurrentProcedureInfo.getProcedureName().equals(procName);
		// void endUltimateInitOrStart(final Dispatcher main, final Procedure initDecl,
		// final String startOrInit) {
		// void endUltimateInitOrStart(final Dispatcher main, final Procedure initDecl,
		// final String startOrInit,
		// final Collection<String> calledProcedures) {
		// for (final String calledProcedure : calledProcedures) {
		// addCallGraphEdge(startOrInit, calledProcedure);
		// }

		// mProcedures.put(startOrInit, initDecl);
		// TODO: rethink this -- is this resetting only about modifies clause? if yes:
		// shouldn't this be handled
		// elsewhere?
		// EDIT: indeed, updates to modifies clauses should be registered with the
		// function handler
		// final ProcedureInfo procInfo = getProcedureInfo(startOrInit);
		// procInfo.resetDeclaration(initDecl);

		// mCurrentProcedureInfo = null;
		//
		// main.mCHandler.endScope();
		endProcedureScope(main);
	}

	public Procedure getProcedureDeclaration(final String procedureName) {
		final BoogieProcedureInfo procInfo = getProcedureInfo(procedureName);
		if (!procInfo.hasDeclaration()) {
			throw new IllegalArgumentException("a procedure of the requested name is not yet known: " + procedureName);
		}
		return procInfo.getDeclaration();
	}

	/**
	 *
	 * @return true iff we (the translation) are currently in global scope. (We are
	 *         in global scope if we are not currently translating the body of a
	 *         function)
	 */
	public boolean isGlobalScope() {
		return mCurrentProcedureInfo == null;
	}

	/**
	 * @return the identifier of the current procedure whose scope we are currently
	 *         in (i.e. we are currently translating the result's procedure body.
	 */
	public String getCurrentProcedureID() {
		if (mCurrentProcedureInfo == null) {
			throw new IllegalStateException("Check for isGlobalScope first");
		}
		return mCurrentProcedureInfo.getProcedureName();
		// if (mCurrentProcedure == null) {
		// return null;
		// }
		// return mCurrentProcedure.getIdentifier();
	}

	// public void addMemoryModelDeclarations(final MemoryModelDeclarations...
	// mmdecls) {
	//
	// final String currentProcId = mCurrentProcedure.getIdentifier();
	// Set<String> str = mCallGraphOld.get(currentProcId);
	// if (str == null) {
	// str = new LinkedHashSet<>();
	// mCallGraphOld.put(currentProcId, str);
	// }
	// for (final MemoryModelDeclarations mmdecl : mmdecls) {
	// str.add(mmdecl.getName());
	// }
	// }

	// public boolean noCurrentProcedure() {
	// return mCurrentProcedure == null;
	// }

	// public void addCallGraphEdge(final String source, final String target) {
	// Set<String> set = mCallGraphOld.get(source);
	// if (set == null) {
	// set = new LinkedHashSet<>();
	// mCallGraphOld.put(source, set);
	// }
	// set.add(target);
	// }

	public CFunction getCFunctionType(final String function) {
		final BoogieProcedureInfo procInfo = getProcedureInfo(function);
		return procInfo.getCType();

		// return mProcedureToCFunctionType.get(function);
	}

	/**
	 *
	 * @param tentativeProcedureName
	 * @return true iff a procedure of the given name is known to the function
	 *         handler
	 */
	public boolean hasProcedure(final String tentativeProcedureName) {
		return mProcedureNameToProcedureInfo.containsKey(tentativeProcedureName);
	}

	@Deprecated
	public void addModifiedGlobal(final String procedureName, final VariableLHS globalBoogieVarName) {
		getProcedureInfo(procedureName).addModifiedGlobal(globalBoogieVarName);
	}

	/**
	 * Adds a modified global for the procedure whose scope we are currently in.
	 *
	 * @param modifiedGlobal
	 */
	@Deprecated
	public void addModifiedGlobal(final VariableLHS modifiedGlobal) {
		if (mCurrentProcedureInfo == null) {
			throw new IllegalStateException();
		}
		mCurrentProcedureInfo.addModifiedGlobal(modifiedGlobal);

	}

	/**
	 * Contains information about a procedure in the target Boogie program.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 */
	static final class BoogieProcedureInfo {

		/**
		 * the procedure's name (in the Boogie program)
		 */
		private final String mProcedureName;

		private CFunction mCType;

		private Procedure mDeclaration;
		private Procedure mImplementation;

		private final Set<VariableLHS> mModifiedGlobals;

		private boolean mModifiedGlobalsIsUsedDefined;

		BoogieProcedureInfo(final String name) {
			mProcedureName = name;
			mModifiedGlobals = new LinkedHashSet<>();
		}

		public void resetCType(final CFunction cFunction) {
			assert mCType != null : "use setCType in this case";
			mCType = cFunction;
		}

		/**
		 * replace the existing declaration with another (refined) one
		 *
		 * @param procDecl
		 */
		public void resetDeclaration(final Procedure declaration) {
			assert declaration.getSpecification() != null;
			assert declaration.getBody() == null;
			mDeclaration = declaration;
		}

		public boolean hasDeclaration() {
			return mDeclaration != null;
		}

		public boolean hasImplementation() {
			return mImplementation != null;
		}

		public boolean hasCType() {
			return mCType != null;
		}

		public void addModifiedGlobals(final Set<VariableLHS> varNames) {
			mModifiedGlobals.addAll(varNames);
		}

		public void addModifiedGlobal(final VariableLHS varName) {
			mModifiedGlobals.add(varName);
		}

		public CFunction getCType() {
			if (mCType == null) {
				throw new IllegalStateException("query hasCType before calling this");
			}
			return mCType;
		}

		public void setCType(final CFunction cType) {
			assert mCType == null : "can only be set once!";
			mCType = cType;
		}

		/**
		 * Update the map procedureToCFunctionType according to the given arguments If a
		 * parameter is null, the corresponding value will not be changed. (for
		 * takesVarArgs, use "false" to change nothing).
		 */
		void updateCFunction(final CType returnType, final CDeclaration[] allParamDecs, final CDeclaration oneParamDec,
				final boolean takesVarArgs) {
			// final CFunction oldCFunction = this.getCType();

			// final CType oldRetType = oldCFunction == null ? null :
			// oldCFunction.getResultType();
			final CType oldRetType = hasCType() ? getCType().getResultType() : null;
			final CDeclaration[] oldInParams =
					// oldCFunction == null ? new CDeclaration[0] :
					// oldCFunction.getParameterTypes();
					hasCType() ? getCType().getParameterTypes() : new CDeclaration[0];
			// final boolean oldTakesVarArgs = oldCFunction == null ? false :
			// oldCFunction.takesVarArgs();
			final boolean oldTakesVarArgs = hasCType() ? getCType().takesVarArgs() : false;

			CType newRetType = oldRetType;
			CDeclaration[] newInParams = oldInParams;
			final boolean newTakesVarArgs = oldTakesVarArgs || takesVarArgs;

			if (allParamDecs != null) { // set a new parameter list
				assert oneParamDec == null;
				newInParams = allParamDecs;
			} else if (oneParamDec != null) { // add a parameter to the list
				assert allParamDecs == null;

				final ArrayList<CDeclaration> ips = new ArrayList<>(Arrays.asList(oldInParams));
				ips.add(oneParamDec);
				newInParams = ips.toArray(new CDeclaration[ips.size()]);
			}
			if (returnType != null) {
				newRetType = returnType;
			}

			if (hasCType()) {
				resetCType(new CFunction(newRetType, newInParams, newTakesVarArgs));
			} else {
				setCType(new CFunction(newRetType, newInParams, newTakesVarArgs));
			}
		}

		public Procedure getDeclaration() {
			if (mDeclaration == null) {
				throw new IllegalStateException("query hasDeclaration() first");
			}
			return mDeclaration;
		}

		public void setDeclaration(final Procedure declaration) {
			assert mDeclaration == null : "can only be set once!";
			assert declaration.getSpecification() != null;
			assert declaration.getBody() == null;
			mDeclaration = declaration;
		}

		public Procedure getImplementation() {
			return mImplementation;
		}

		public void setImplementation(final Procedure implementation) {
			assert mImplementation == null : "can only be set once!";
			assert implementation.getSpecification() == null;
			assert implementation.getBody() != null;
			mImplementation = implementation;
		}

		public boolean isModifiedGlobalsIsUsedDefined() {
			return mModifiedGlobalsIsUsedDefined;
		}

		public void setModifiedGlobalsIsUsedDefined(final boolean modifiedGlobalsIsUsedDefined) {
			mModifiedGlobalsIsUsedDefined = modifiedGlobalsIsUsedDefined;
		}

		public String getProcedureName() {
			return mProcedureName;
		}

		public Set<VariableLHS> getModifiedGlobals() {
			return Collections.unmodifiableSet(mModifiedGlobals);
		}

		@Override
		public String toString() {
			return mProcedureName + " : " + mCType;
		}
	}

	private Specification constructModifiesSpecification(final CACSLLocation loc, final boolean isFree,
			final VariableLHS[] modifyList) {
		final Set<VariableLHS> modifiedGlobals = new LinkedHashSet<>(Arrays.asList(modifyList));
		final Set<VariableLHS> mgFiltered = filterDuplicateVariableLHSs(modifiedGlobals);
		return new ModifiesSpecification(loc, isFree, mgFiltered.toArray(new VariableLHS[mgFiltered.size()]));
	}

	public Body constructBody(final ILocation loc, final VariableDeclaration[] localDeclarations,
			final Statement[] statements, final String procName) {
		assert !isGlobalScope() : "should be in the scope of the currently created procedure body..";

		final BoogieProcedureInfo procInfo = getProcedureInfo(procName);

		final Collection<Statement> callsAndAssignments =
				new CallAndAssignmentStatementFinder().getCallsAndAssignments(statements);
//		for (final Statement statement : statements) {
		for (final Statement statement : callsAndAssignments) {
			if (statement instanceof CallStatement) {
				registerCallStatement((CallStatement) statement, procInfo);
			}
			if (statement instanceof AssignmentStatement) {
				registerAssignmentStatement((AssignmentStatement) statement, procInfo);
			}
		}
		return new Body(loc, localDeclarations, statements);
	}

	private void registerAssignmentStatement(final AssignmentStatement statement, final BoogieProcedureInfo procInfo) {
		for (final LeftHandSide lhs : statement.getLhs()) {
			final VariableLHS modifiedGlobal = new BoogieGlobalLhsFinder().getGlobalId(lhs);
			if (modifiedGlobal != null) {
				procInfo.addModifiedGlobal(modifiedGlobal);
			}
		}
	}

	private void registerCallStatement(final CallStatement statement, final BoogieProcedureInfo caller) {
		for (final LeftHandSide lhs : statement.getLhs()) {
			final VariableLHS modifiedGlobal = new BoogieGlobalLhsFinder().getGlobalId(lhs);
			if (modifiedGlobal != null) {
				// addModifiedGlobal(modifiedGlobal);
				caller.addModifiedGlobal(modifiedGlobal);
			}
		}
		final BoogieProcedureInfo callee = getOrConstructProcedureInfo(statement.getMethodName());
		registerCall(caller, callee);
	}

	/**
	 * Essentially this method is to remind the programmer that he or she has to
	 * give modified globals for an ensures specification manually.
	 *
	 * @param loc
	 * @param isFree
	 * @param formula
	 * @param modifiedGlobals
	 * @return
	 */
	public EnsuresSpecification constructEnsuresSpecification(final ILocation loc, final boolean isFree,
			final Expression formula, final Set<VariableLHS> modifiedGlobals) {
		// // TODO: what is the criterion for when an ensures clause constitutes a
		// modification??
		// // --> probably we have to set this manually!...
		// if (!isFree) {
		// final Set<IdentifierExpression> modifiedGlobals =
		// new
		// BoogieGlobalIdentifierExpressionsFinder().getGlobalIdentifierExpressions(formula);
		// for (final IdentifierExpression modifiedGlobal : modifiedGlobals) {
		// addModifiedGlobal((VariableLHS)
		// CTranslationUtil.convertExpressionToLHS(modifiedGlobal));
		// }
		// }
		// modifiedGlobals.forEach(this::addModifiedGlobal);
		// final BoogieProcedureInfo procInfo = getOrConstructProcedureInfo(procName);
		final BoogieProcedureInfo procInfo = mCurrentProcedureInfo;
		procInfo.addModifiedGlobals(modifiedGlobals);

		return new EnsuresSpecification(loc, isFree, formula);
	}

	public void addSpecificationsToCurrentProcedure(final List<Specification> specs) {
		assert !isGlobalScope();
		final BoogieProcedureInfo procInfo = mCurrentProcedureInfo;
		final Procedure oldDecl = procInfo.getDeclaration();

		final List<Specification> newSpecs = new ArrayList<>();
		newSpecs.addAll(Arrays.asList(oldDecl.getSpecification()));
		newSpecs.addAll(specs);

		final Procedure newDecl = new Procedure(oldDecl.getLoc(), oldDecl.getAttributes(), oldDecl.getIdentifier(),
				oldDecl.getTypeParams(), oldDecl.getInParams(), oldDecl.getOutParams(),
				newSpecs.toArray(new Specification[newSpecs.size()]), null);

		procInfo.resetDeclaration(newDecl);
	}

	BoogieProcedureInfo getCurrentProcedureInfo() {
		return mCurrentProcedureInfo;
	}

	public boolean isCalledBeforeDeclared(final BoogieProcedureInfo definedProcInfo) {
		return mMethodsCalledBeforeDeclared.contains(definedProcInfo);
	}

	public void registerCalledBeforeDeclaredFunction(final BoogieProcedureInfo procInfo) {
		mMethodsCalledBeforeDeclared.add(procInfo);
	}


	class CallAndAssignmentStatementFinder extends BoogieVisitor {

		Collection<Statement> mResult = new ArrayList<>();

		@Override
		protected void visit(final CallStatement statement) {
			mResult.add(statement);
			super.visit(statement);
		}

		@Override
		protected void visit(final AssignmentStatement statement) {
			mResult.add(statement);
			super.visit(statement);
		}

		Collection<Statement> getCallsAndAssignments(final Statement[] inputStatements) {
			processStatements(inputStatements);

			return mResult;
		}

	}

}
