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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVisitor;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ForkStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.BoogieGlobalLhsFinder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.StandardFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UndeclaredFunctionException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.util.TransitiveClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.LinkedHashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;

/**
 * Manages the Boogie procedures of the translated program.
 * <p>
 * Boogie procedures are inserted into the translated program from several sources:
 * <ul>
 * <li>translations of C functions ({@link CHandler}, {@link FunctionHandler})
 * <li>helper procedures from the memory model ({@link MemoryHandler})
 * <li>when we provide a Boogie model for a standard C function ({@link StandardFunctionHandler})
 * <li>Ultimate.start and Ultimate.init ({@link PostProcessor})
 * </ul>
 * Note that at the moment this manages procedure declarations. Procedure implementations are passed around elsewhere.
 * (We do not use the Boogie feature to have declaration and implementation in one.)
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ProcedureManager {

	private final Set<BoogieProcedureInfo> mMethodsCalledBeforeDeclared;

	private final Map<String, BoogieProcedureInfo> mProcedureNameToProcedureInfo;
	private final LinkedHashRelation<BoogieProcedureInfo, BoogieProcedureInfo> mInverseCallGraph;

	private BoogieProcedureInfo mCurrentProcedureInfo;

	private final ILogger mLogger;

	private final TranslationSettings mSettings;

	public ProcedureManager(final ILogger logger, final TranslationSettings settings) {
		mLogger = logger;
		mSettings = settings;
		mMethodsCalledBeforeDeclared = new LinkedHashSet<>();
		mProcedureNameToProcedureInfo = new LinkedHashMap<>();
		mInverseCallGraph = new LinkedHashRelation<>();
	}

	void beginProcedureScope(final CHandler main, final BoogieProcedureInfo currentProcInfo) {
		assert currentProcInfo != null;
		mCurrentProcedureInfo = currentProcInfo;
		main.beginScope();
	}

	void endProcedureScope(final CHandler main) {
		mCurrentProcedureInfo = null;
		main.endScope();
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
	 * This method is expected to be called from CHandler.visit(..TranslationUnit) after all procedures have been
	 * registered in the FunctionHandler.
	 * <p>
	 * Returns declarations for all procedures that will appear in the translated program. Ensures that the modifies
	 * clauses of all procedures are transitive with respect to the call graph.
	 * <p>
	 * Special case regarding memory models: if one memory-array is included, all active memory arrays have to be
	 * included (f.i. we have procedure modifies memory_int, and memoryHandler.isFloatMMArray == true, and
	 * memoryHandler.isIntMMArray == true, memoryHandler.isPointerMMArray == false, then we have to add memory_real to
	 * the modifies clause of procedure
	 *
	 * @return procedure declarations
	 */
	public List<Declaration> computeFinalProcedureDeclarations(final MemoryHandler memoryHandler) {
		final BoogieProcedureInfo notDeclaredProcedure = isEveryCalledProcedureDeclared();
		if (notDeclaredProcedure != null) {
			throw new UndeclaredFunctionException(null, "a function that is called in the program "
					+ "is not declared in the program: " + notDeclaredProcedure.getProcedureName());
		}

		/**
		 * The base graph for the computation of strongly connected components (SCCs) is the inverse call graph. I.e.,
		 * in the sense of this graph, the successors of a procedure are its callers.
		 */
		final ISuccessorProvider<BoogieProcedureInfo> successorProvider =
				new ISuccessorProvider<BoogieProcedureInfo>() {
					@Override
					public Iterator<BoogieProcedureInfo> getSuccessors(final BoogieProcedureInfo node) {
						return mInverseCallGraph.getImage(node).iterator();
					}
				};

		final Set<BoogieProcedureInfo> allProcedures = new HashSet<>(mProcedureNameToProcedureInfo.values());
		final Function<BoogieProcedureInfo, Set<VariableLHS>> initialProcToModGlobals = p -> p.getModifiedGlobals();
		final Map<BoogieProcedureInfo, Set<VariableLHS>> closedProcToModGlobals =
				TransitiveClosure.computeClosure(mLogger, allProcedures, initialProcToModGlobals, successorProvider);

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
				final Set<VariableLHS> currModClause = closedProcToModGlobals.get(procInfo);
				assert currModClause != null : "No modifies clause proc " + procedureName;

				procInfo.addModifiedGlobals(currModClause);

				newSpec = Arrays.copyOf(oldSpec, oldSpec.length + 1);

				{
					/*
					 * add missing heap arrays If the procedure modifies one heap array, we add all heap arrays. This is
					 * a workaround. We cannot add all procedures immediately, because we do not know all heap arrays in
					 * advance since they are added lazily on demand.
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
						modifyList[i++] = modifyEntry;
					}
				}
				newSpec[oldSpec.length] = constructModifiesSpecification(loc, false, modifyList);
			}

			final Specification[] newSpecWithExtraEnsuresClauses;
			if (memoryHandler.getRequiredMemoryModelFeatures().isMemoryModelInfrastructureRequired()
					&& (mSettings.checkAllocationPurity() || (mSettings.getCheckedMethod().equals(SFO.EMPTY)
							|| mSettings.getCheckedMethod().equals(procedureName))
							&& mSettings.checkMemoryLeakInMain())) {
				// add a specification to check for memory leaks

				final Expression vIe = memoryHandler.getValidArray(loc);

				final int nrSpec = newSpec.length;
				final Check check = new Check(Check.Spec.MEMORY_LEAK);
				final ILocation ensLoc = LocationFactory.createLocation(loc, check);
				newSpecWithExtraEnsuresClauses = Arrays.copyOf(newSpec, nrSpec + 1);
				newSpecWithExtraEnsuresClauses[nrSpec] = new EnsuresSpecification(ensLoc, false,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, vIe,
								ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, vIe)));
				check.annotate(newSpecWithExtraEnsuresClauses[nrSpec]);
				if (mSettings.isSvcompMemtrackCompatibilityMode()) {
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
	 * only keep variable lhss that refer to the same global variable, i.e., keep only one per identifier String.
	 *
	 * @return
	 */
	private static Set<VariableLHS> filterDuplicateVariableLHSs(final Set<VariableLHS> input) {
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

	void registerCall(final BoogieProcedureInfo caller, final BoogieProcedureInfo callee) {
		if (!callee.hasDeclaration()) {
			mMethodsCalledBeforeDeclared.add(callee);
		}

		mInverseCallGraph.addPair(callee, caller);
	}

	/**
	 * Checks, whether all procedures that are being called in C, were eventually declared within the C program.
	 *
	 * @return null if all called procedures were declared, otherwise the identifier of one procedure that was called
	 *         but not declared.
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
	 * Announces the beginning of the declaration of a custom procedure. A custom procedure is a procedure that is
	 * introduced by the translation and has no direct counterpart in the translated C program. Examples are
	 * Ultimate.start, Ultimate.init, and the procedures introduces by the memory model.
	 *
	 * @param main
	 * @param loc
	 * @param procedureName
	 * @param procedureDecl
	 *            initial declaration for the procedure, should contain the signature, may be reset later for adding
	 *            specifications; modifies specification will be generated by FunctionHandler like for all procedures.
	 */
	void beginCustomProcedure(final CHandler main, final ILocation loc, final String procedureName,
			final Procedure procedureDecl) {
		final BoogieProcedureInfo procInfo = getOrConstructProcedureInfo(procedureName);
		procInfo.setDeclaration(procedureDecl);
		beginProcedureScope(main, procInfo);
	}

	/**
	 *
	 * @param main
	 * @param initDecl
	 *            note this must be a pure declaration, i.e., its body must be null
	 * @param procName
	 * @param calledProcedures
	 */
	void endCustomProcedure(final CHandler main, final String procName) {
		assert mCurrentProcedureInfo.getProcedureName().equals(procName);
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
	 * @return true iff we (the translation) are currently in global scope. (We are in global scope if we are not
	 *         currently translating the body of a function)
	 */
	public boolean isGlobalScope() {
		return mCurrentProcedureInfo == null;
	}

	/**
	 * @return the identifier of the current procedure whose scope we are currently in (i.e. we are currently
	 *         translating the result's procedure body.
	 */
	public String getCurrentProcedureID() {
		if (mCurrentProcedureInfo == null) {
			throw new IllegalStateException("Check for isGlobalScope first");
		}
		return mCurrentProcedureInfo.getProcedureName();
	}

	public CFunction getCFunctionType(final String function) {
		final BoogieProcedureInfo procInfo = getProcedureInfo(function);
		return procInfo.getCType();
	}

	/**
	 *
	 * @param tentativeProcedureName
	 * @return true iff a procedure of the given name is known to the function handler
	 */
	public boolean hasProcedure(final String tentativeProcedureName) {
		return mProcedureNameToProcedureInfo.containsKey(tentativeProcedureName);
	}

	private static Specification constructModifiesSpecification(final CACSLLocation loc, final boolean isFree,
			final VariableLHS[] modifyList) {
		final Set<VariableLHS> modifiedGlobals = new LinkedHashSet<>(Arrays.asList(modifyList));
		final Set<VariableLHS> mgFiltered = filterDuplicateVariableLHSs(modifiedGlobals);
		return new ModifiesSpecification(loc, isFree, mgFiltered.toArray(new VariableLHS[mgFiltered.size()]));
	}

	public Body constructBody(final ILocation loc, final VariableDeclaration[] localDeclarations,
			final Statement[] statements, final String procName) {
		final BoogieProcedureInfo procInfo = getProcedureInfo(procName);

		final Collection<Statement> callsAndAssignments =
				new CallAndAssignmentStatementFinder().getCallsAndAssignments(statements);
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

	private static void registerAssignmentStatement(final AssignmentStatement statement,
			final BoogieProcedureInfo procInfo) {
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
				caller.addModifiedGlobal(modifiedGlobal);
			}
		}
		final BoogieProcedureInfo callee = getOrConstructProcedureInfo(statement.getMethodName());
		registerCall(caller, callee);
	}

	public void registerForkStatement(final ForkStatement fs) {
		final String currentProcedure = getCurrentProcedureID();
		final BoogieProcedureInfo procInfoOfCurrentProcedure = getProcedureInfo(currentProcedure);
		final BoogieProcedureInfo procInfoOfForkedProcedure = getProcedureInfo(fs.getProcedureName());
		registerCall(procInfoOfCurrentProcedure, procInfoOfForkedProcedure);
	}

	/**
	 * Essentially this method is to remind the programmer that he or she has to give modified globals for an ensures
	 * specification manually.
	 *
	 * @param loc
	 * @param isFree
	 * @param formula
	 * @param modifiedGlobals
	 * @return
	 */
	public EnsuresSpecification constructEnsuresSpecification(final ILocation loc, final boolean isFree,
			final Expression formula, final Set<VariableLHS> modifiedGlobals) {
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

	public Set<CFunction> getAllFunctionSignatures() {
		return mProcedureNameToProcedureInfo.entrySet().stream().map(Entry::getValue).filter(x -> x.hasCType())
				.map(x -> x.getCType()).collect(Collectors.toSet());
	}

	/**
	 * Contains information about a procedure in the target Boogie program.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 */
	static final class BoogieProcedureInfo {

		/**
		 * the procedure's name in the Boogie program
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

		/**
		 * Add a parameter to the current function.
		 */
		public void updateCFunctionAddParam(final CDeclaration param) {
			final CDeclaration[] newParams;
			if (hasCType()) {
				final CDeclaration[] oldParams = getCType().getParameterTypes();
				newParams = Arrays.copyOf(oldParams, oldParams.length + 1);
				newParams[newParams.length - 1] = param;
			} else {
				newParams = new CDeclaration[] { param };
			}
			updateCFunctionReplaceParams(newParams);
		}

		/**
		 * Replace all parameter of the current function with the specified ones.
		 */
		public void updateCFunctionReplaceParams(final CDeclaration[] params) {
			if (hasCType()) {
				mCType = mCType.newParameter(params);
			} else {
				mCType = CFunction.createEmptyCFunction().newParameter(params);
			}
		}

		public void updateCFunction(final CFunction funcType) {
			mCType = funcType;
		}

		public Procedure getDeclaration() {
			if (mDeclaration == null) {
				throw new IllegalStateException("query hasDeclaration() first");
			}
			return mDeclaration;
		}

		public void setDefaultDeclarationAndCType(final ILocation loc, final ASTType intType) {
			setDefaultDeclaration(loc, intType);
			mCType = CFunction.createDefaultCFunction();
		}

		/**
		 * Sets the Boogie declaration that corresponds to the C declaration "int foo()".
		 */
		void setDefaultDeclaration(final ILocation loc, final ASTType intType) {
			setDeclaration(new Procedure(loc, new Attribute[0], mProcedureName, new String[0], new VarList[0],
					new VarList[] { new VarList(loc, new String[] { SFO.RES }, intType) }, new Specification[0], null));
		}

		void setDeclaration(final Procedure declaration) {
			assert mDeclaration == null : "can only be set once!";
			assert declaration.getSpecification() != null;
			assert declaration.getBody() == null;
			mDeclaration = declaration;
		}

		public Procedure getImplementation() {
			return mImplementation;
		}

		void setImplementation(final Procedure implementation) {
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
