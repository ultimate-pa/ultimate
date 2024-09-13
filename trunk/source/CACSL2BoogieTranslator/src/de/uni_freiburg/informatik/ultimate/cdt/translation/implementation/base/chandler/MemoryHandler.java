/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
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
/**
 * Class that handles translation of memory related operations.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;
import java.util.stream.Collectors;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.StatementFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AtomicStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BreakStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.WhileStatement;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructExpanderUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.DataRaceChecker;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.BaseMemoryModel.ReadWriteDefinition;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.memoryhandler.ConstructMemcpyOrMemmove;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.memoryhandler.ConstructRealloc;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfoBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CNamed;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitiveCategory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStructOrUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValueFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.MemoryModel;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * @author Markus Lindenmann
 */
public class MemoryHandler {

	public enum MemoryArea {
		STACK, HEAP,;

		MemoryModelDeclarations getMemoryModelDeclaration() {
			switch (this) {
			case HEAP:
				return MemoryModelDeclarations.ULTIMATE_ALLOC_HEAP;
			case STACK:
				return MemoryModelDeclarations.ULTIMATE_ALLOC_STACK;
			default:
				throw new AssertionError();
			}
		}
	}

	private enum HeapWriteMode {
		STORE_CHECKED, STORE_UNCHECKED, SELECT
	}

	private static final boolean SUPPORT_FLOATS_ON_HEAP = true;
	private static final String FLOAT_ON_HEAP_UNSOUND_MESSAGE =
			"Analysis for floating types on heap by default disabled (soundness first).";

	/**
	 * The "~size" variable identifier.
	 */
	private static final String SIZE = "~size";
	/**
	 * The "~addr" variable identifier.
	 */
	private static final String ADDR = "~addr";

	/**
	 * Add also implementations of malloc, free, write and read functions. TODO: details
	 */
	private static final boolean ADD_IMPLEMENTATIONS = false;

	/**
	 * See {@link MemoryModelDeclarations#ULTIMATE_ALLOC_INIT}.
	 */
	public static final boolean FIXED_ADDRESSES_FOR_INITIALIZATION = true;

	// needed for adding modifies clauses
	private final ITypeHandler mTypeHandler;

	/**
	 * This set contains those pointers that we have to malloc at the beginning of the current scope;
	 */
	private final LinkedScopedHashMap<LocalLValueILocationPair, Integer> mVariablesToBeMalloced;
	/**
	 * This set contains those pointers that we have to free at the end of the current scope;
	 */
	private final LinkedScopedHashMap<LocalLValueILocationPair, Integer> mVariablesToBeFreed;

	private final ExpressionTranslation mExpressionTranslation;

	private final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	private final TypeSizes mTypeSizes;
	private final RequiredMemoryModelFeatures mRequiredMemoryModelFeatures;
	private final BaseMemoryModel mMemoryModel;
	private final INameHandler mNameHandler;
	private final IBooleanArrayHelper mBooleanArrayHelper;
	private final ProcedureManager mProcedureManager;
	private final Map<MemoryModelDeclarations, MemoryModelDeclarationInfo> mMemoryModelDeclarationInfos;

	private final AuxVarInfoBuilder mAuxVarInfoBuilder;
	private final TranslationSettings mSettings;

	/**
	 * See {@link MemoryModelDeclarations#ULTIMATE_ALLOC_INIT}
	 */
	private int mFixedAddressCounter = 1;

	/**
	 * Pre-run constructor.
	 *
	 */
	public MemoryHandler(final TypeSizes typeSizes, final INameHandler nameHandler,
			final boolean smtBoolArrayWorkaround, final ITypeHandler typeHandler,
			final ExpressionTranslation expressionTranslation, final ProcedureManager procedureManager,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final AuxVarInfoBuilder auxVarInfoBuilder,
			final TranslationSettings settings) {
		mTypeHandler = typeHandler;
		mTypeSizes = typeSizes;
		mExpressionTranslation = expressionTranslation;
		mNameHandler = nameHandler;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mProcedureManager = procedureManager;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mSettings = settings;

		mRequiredMemoryModelFeatures = new RequiredMemoryModelFeatures();
		if (smtBoolArrayWorkaround) {
			if (mSettings.isBitvectorTranslation()) {
				mBooleanArrayHelper = new BooleanArrayHelper_Bitvector();
			} else {
				mBooleanArrayHelper = new BooleanArrayHelper_Integer();
			}
		} else {
			mBooleanArrayHelper = new BooleanArrayHelper_Bool();
		}

		mMemoryModel = getMemoryModel(settings.isBitvectorTranslation(), settings.getMemoryModelPreference());
		mVariablesToBeMalloced = new LinkedScopedHashMap<>();
		mVariablesToBeFreed = new LinkedScopedHashMap<>();
		mMemoryModelDeclarationInfos = new LinkedHashMap<>();
	}

	/**
	 * Main run constructor
	 */
	public MemoryHandler(final MemoryHandler prerunMemoryHandler, final TypeSizes typeSizes,
			final INameHandler nameHandler, final ITypeHandler typeHandler,
			final ExpressionTranslation expressionTranslation, final ProcedureManager procedureManager,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer, final AuxVarInfoBuilder auxVarInfoBuilder,
			final TranslationSettings settings) {
		mTypeHandler = typeHandler;
		mTypeSizes = typeSizes;
		mExpressionTranslation = expressionTranslation;
		mNameHandler = nameHandler;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mProcedureManager = procedureManager;
		mAuxVarInfoBuilder = auxVarInfoBuilder;
		mSettings = settings;

		mRequiredMemoryModelFeatures = new RequiredMemoryModelFeatures();// prerunMemoryHandler.mRequiredMemoryModelFeatures;
		mBooleanArrayHelper = prerunMemoryHandler.mBooleanArrayHelper;
		mMemoryModel = prerunMemoryHandler.mMemoryModel;
		mVariablesToBeMalloced = prerunMemoryHandler.mVariablesToBeMalloced;
		mVariablesToBeFreed = prerunMemoryHandler.mVariablesToBeFreed;
		mMemoryModelDeclarationInfos = prerunMemoryHandler.mMemoryModelDeclarationInfos;
	}

	public RequiredMemoryModelFeatures getRequiredMemoryModelFeatures() {
		return mRequiredMemoryModelFeatures;
	}

	public BaseMemoryModel getMemoryModel() {
		return mMemoryModel;
	}

	public Expression calculateSizeOf(final ILocation loc, final CType cType) {
		return mTypeSizeAndOffsetComputer.constructBytesizeExpression(loc, cType);
	}

	// TODO: This handling is quite imprecise and does not even consider cType
	public ExpressionResult handleAlignOf(final ILocation loc, final CType cType, final CType resultType) {
		final ExpressionResultBuilder builder = new ExpressionResultBuilder();
		builder.addOverapprox(new Overapprox("alignof", loc));
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.NONDET);
		builder.addAuxVarWithDeclaration(auxvar);
		builder.setLrValue(new RValue(auxvar.getExp(), resultType));
		return builder.build();
	}

	/**
	 * Returns declarations needed for the memory model (right now we use the Hoenicke-Lindenmann memory model).
	 * Depending on the translated program this may include any or all of the following:
	 * <li>declarations of the arrays #valid, #length, #memory_int, etc.
	 * <li>declarations of the procedures Ultimate.alloc, Ultimate.dealloc, read_int, write_int, etc.
	 *
	 * Note that this method only returns procedure implementations (if there are any). The corresponding declarations
	 * are introduced by registering the procedures in the FunctionHandler. The FunctionHandler will add them to the
	 * program.
	 *
	 * @param main
	 *            a reference to the main IDispatcher.
	 * @param tuLoc
	 *            location to use for declarations. Usually this will be the location of the TranslationUnit.
	 * @return a set of declarations.
	 */
	public List<Declaration> declareMemoryModelInfrastructure(final CHandler main, final ILocation tuLoc,
			final DataRaceChecker dataRaceChecker) {
		mRequiredMemoryModelFeatures.finish(mSettings);

		if (!mRequiredMemoryModelFeatures.isMemoryModelInfrastructureRequired()) {
			return Collections.emptyList();
		}

		final ArrayList<Declaration> decl = new ArrayList<>();

		decl.add(constructValidArrayDeclaration());
		decl.add(constuctLengthArrayDeclaration());

		final Collection<HeapDataArray> heapDataArrays = mMemoryModel.getDataHeapArrays(mRequiredMemoryModelFeatures);

		{
			// add memory arrays and read/write procedures
			for (final HeapDataArray heapDataArray : heapDataArrays) {
				decl.add(constructMemoryArrayDeclaration(tuLoc, heapDataArray.getName(), heapDataArray.getASTType()));
				// create and add read and write procedure
				decl.addAll(constructWriteProcedures(main, tuLoc, heapDataArrays, heapDataArray));
				decl.addAll(constructReadProcedures(main, tuLoc, heapDataArray));

			}
		}

		{
			// add store function (to be able to assign subarrays at pointer base addresses)
			for (final CPrimitives prim : mRequiredMemoryModelFeatures.getDataOnHeapRequired()) {
				if (mRequiredMemoryModelFeatures.isDataOnHeapStoreFunctionRequired(prim)) {
					declareDataOnHeapStoreFunction(mMemoryModel.getDataHeapArray(prim));
					declareDataOnHeapSelectFunction(mMemoryModel.getDataHeapArray(prim));
				}
			}
			if (mRequiredMemoryModelFeatures.isPointerOnHeapStoreFunctionRequired()) {
				declareDataOnHeapStoreFunction(mMemoryModel.getPointerHeapArray());
				declareDataOnHeapSelectFunction(mMemoryModel.getPointerHeapArray());
			}
		}

		{
			// add init function (interface to smt const arrays)
			for (final CPrimitives prim : mRequiredMemoryModelFeatures.getDataOnHeapRequired()) {
				if (mRequiredMemoryModelFeatures.isDataOnHeapInitFunctionRequired(prim)) {
					declareDataOnHeapInitFunction(mMemoryModel.getDataHeapArray(prim));
				}
			}
			if (mRequiredMemoryModelFeatures.isPointerOnHeapInitFunctionRequired()) {
				declareDataOnHeapInitFunction(mMemoryModel.getPointerHeapArray());
			}
		}

		decl.addAll(declareDeallocation(main, tuLoc));

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_ALLOC_STACK)) {
			decl.addAll(declareMalloc(main, mTypeHandler, tuLoc, MemoryArea.STACK));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_ALLOC_INIT)) {
			declareAllocInit(main, mTypeHandler, tuLoc);
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_ALLOC_HEAP)) {
			decl.addAll(declareMalloc(main, mTypeHandler, tuLoc, MemoryArea.HEAP));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_MEMSET)) {
			decl.addAll(declareMemset(main, heapDataArrays));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_MEMINIT)) {
			decl.addAll(declareUltimateMeminit(main, heapDataArrays));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_MEMCPY)) {
			final ConstructMemcpyOrMemmove cmcom = new ConstructMemcpyOrMemmove(this, mProcedureManager,
					(TypeHandler) mTypeHandler, mTypeSizeAndOffsetComputer, mExpressionTranslation, mAuxVarInfoBuilder,
					mTypeSizes, dataRaceChecker);
			decl.addAll(cmcom.declareMemcpyOrMemmove(main, MemoryModelDeclarations.C_MEMCPY));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_MEMMOVE)) {
			final ConstructMemcpyOrMemmove cmcom = new ConstructMemcpyOrMemmove(this, mProcedureManager,
					(TypeHandler) mTypeHandler, mTypeSizeAndOffsetComputer, mExpressionTranslation, mAuxVarInfoBuilder,
					mTypeSizes, dataRaceChecker);
			decl.addAll(cmcom.declareMemcpyOrMemmove(main, MemoryModelDeclarations.C_MEMMOVE));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_STRCPY)) {
			decl.addAll(declareStrCpy(main, heapDataArrays));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_REALLOC)) {
			final ConstructRealloc cr = new ConstructRealloc(this, mProcedureManager, (TypeHandler) mTypeHandler,
					mTypeSizeAndOffsetComputer, mExpressionTranslation);
			decl.addAll(cr.declareRealloc(main, heapDataArrays));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_FORK_COUNT)) {
			decl.add(declarePthreadsForkCount(tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX)) {
			decl.add(declarePThreadsMutexArray(tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK)) {
			decl.addAll(declarePthreadMutexLock(main, mTypeHandler, tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_UNLOCK)) {
			decl.addAll(declarePthreadMutexUnlock(main, mTypeHandler, tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_TRYLOCK)) {
			decl.addAll(declarePthreadMutexTryLock(main, mTypeHandler, tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK)) {
			decl.add(declarePthreadRwLock(tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_READLOCK)) {
			decl.addAll(declarePthreadRwLockReadLock(main, mTypeHandler, tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_WRITELOCK)) {
			decl.addAll(declarePthreadRwLockWriteLock(main, mTypeHandler, tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_UNLOCK)) {
			decl.addAll(declarePthreadRwLockUnlock(main, mTypeHandler, tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER)) {
			decl.add(constructStackHeapBarrierConstant());
		}
		assert assertContainsNodeProcedureDeclarations(decl) : "add procedure declarations via function handler!";
		return decl;
	}

	public CallStatement constructUltimateMeminitCall(final ILocation loc, final Expression amountOfFields,
			final Expression sizeOfFields, final Expression product, final Expression pointer) {
		return constructCall(MemoryModelDeclarations.ULTIMATE_MEMINIT, loc, null, pointer, amountOfFields, sizeOfFields,
				product);
	}

	/**
	 * Returns call to our memset procedure and announces that memset is required by our memory model.
	 */
	public CallStatement constructUltimateMemsetCall(final ILocation loc, final Expression pointer,
			final Expression value, final Expression amount, final VariableLHS resVar) {
		return constructCall(MemoryModelDeclarations.C_MEMSET, loc, resVar, pointer, value, amount);
	}

	// calls to functions for locks should be atomic, for sound data race detection
	private static AtomicStatement makeAtomic(final ILocation loc, final Statement statement) {
		return new AtomicStatement(loc, new Statement[] { statement });
	}

	public Statement constructPthreadMutexLockCall(final ILocation loc, final Expression pointer,
			final VariableLHS variableLHS) {
		return makeAtomic(loc,
				constructCall(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK, loc, variableLHS, pointer));
	}

	public Statement constructPthreadMutexUnlockCall(final ILocation loc, final Expression pointer,
			final VariableLHS variableLHS) {
		return makeAtomic(loc,
				constructCall(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_UNLOCK, loc, variableLHS, pointer));
	}

	public Statement constructPthreadMutexTryLockCall(final ILocation loc, final Expression pointer,
			final VariableLHS variableLHS) {
		return makeAtomic(loc,
				constructCall(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_TRYLOCK, loc, variableLHS, pointer));
	}

	public Statement constructPthreadRwLockReadLockCall(final ILocation loc, final Expression pointer,
			final VariableLHS variableLHS) {
		return makeAtomic(loc,
				constructCall(MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_READLOCK, loc, variableLHS, pointer));
	}

	public Statement constructPthreadRwLockWriteLockCall(final ILocation loc, final Expression pointer,
			final VariableLHS variableLHS) {
		return makeAtomic(loc,
				constructCall(MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_WRITELOCK, loc, variableLHS, pointer));
	}

	public Statement constructPthreadRwLockUnlockCall(final ILocation loc, final Expression pointer,
			final VariableLHS variableLHS) {
		return makeAtomic(loc,
				constructCall(MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_UNLOCK, loc, variableLHS, pointer));
	}

	private CallStatement constructCall(final MemoryModelDeclarations decl, final ILocation loc,
			final VariableLHS variableLHS, final Expression... params) {
		requireMemoryModelFeature(decl);
		final VariableLHS[] lhs = variableLHS == null ? new VariableLHS[0] : new VariableLHS[] { variableLHS };
		return StatementFactory.constructCallStatement(loc, false, lhs, decl.getName(), params);
	}

	/**
	 * Construct a Boogie statement of the following form. arrayIdentifier[index] := value; TODO 2017-01-07 Matthias:
	 * This method is not directly related to the MemoryHandler and should probably moved to a some class for utility
	 * functions. But {@link MemoryHandler#constructOneDimensionalArrayAccess} and
	 * {@link MemoryHandler#constructOneDimensionalArrayStore} should be moved to the same class.
	 */
	public static AssignmentStatement constructOneDimensionalArrayUpdate(final ILocation loc, final Expression index,
			final VariableLHS arrayLhs, final Expression value) {
		final LeftHandSide[] lhs = new LeftHandSide[] {
				ExpressionFactory.constructNestedArrayLHS(loc, arrayLhs, new Expression[] { index }) };
		final Expression[] rhs = new Expression[] { value };
		final AssignmentStatement assignment = StatementFactory.constructAssignmentStatement(loc, lhs, rhs);
		return assignment;
	}

	/**
	 * Construct expression that states that the base address of ptr is valid. Depending on the settings this expression
	 * is one of the following
	 * <ul>
	 * <li>#valid[#ptr!base]
	 * <li>#valid[#ptr!base] == 1
	 * <li>#valid[#ptr!base] == 1bv1
	 * </ul>
	 */
	public Expression constructPointerBaseValidityCheckExpr(final ILocation loc, final Expression ptr) {
		final Expression ptrBase = getPointerBaseAddress(ptr, loc);
		final ArrayAccessExpression aae = ExpressionFactory.constructNestedArrayAccessExpression(loc,
				getValidArray(loc), new Expression[] { ptrBase });
		final Expression isValid = mBooleanArrayHelper.compareWithTrue(aae);
		return isValid;
	}

	/**
	 * @param loc
	 *            location of translation unit
	 * @return new IdentifierExpression that represents the <em>#length array</em>
	 */
	public Expression getLengthArray(final ILocation loc) {
		return getMemoryModelFeatureExpression(loc, MemoryModelDeclarations.ULTIMATE_LENGTH);
	}

	/**
	 * @param loc
	 *            location of translation unit
	 * @return new IdentifierExpression that represents the <em>#length array</em>
	 */
	public VariableLHS getLengthArrayLhs(final ILocation loc) {
		return getMemoryModelFeatureLhs(loc, MemoryModelDeclarations.ULTIMATE_LENGTH);
	}

	/**
	 * @param loc
	 *            location of translation unit
	 * @return new IdentifierExpression that represents the <em>#valid array</em>
	 */
	public Expression getValidArray(final ILocation loc) {
		return getMemoryModelFeatureExpression(loc, MemoryModelDeclarations.ULTIMATE_VALID);
	}

	public VariableLHS getValidArrayLhs(final ILocation loc) {
		return getMemoryModelFeatureLhs(loc, MemoryModelDeclarations.ULTIMATE_VALID);
	}

	public Expression getStackHeapBarrier(final ILocation loc) {
		return getMemoryModelFeatureExpression(loc, MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER);
	}

	public Expression getMemoryRaceArray(final ILocation loc) {
		return getMemoryModelFeatureExpression(loc, MemoryModelDeclarations.ULTIMATE_DATA_RACE_MEMORY);
	}

	public VariableLHS getMemoryRaceArrayLhs(final ILocation loc) {
		return getMemoryModelFeatureLhs(loc, MemoryModelDeclarations.ULTIMATE_DATA_RACE_MEMORY);
	}

	private Expression getMemoryModelFeatureExpression(final ILocation loc, final MemoryModelDeclarations decl) {
		requireMemoryModelFeature(decl);
		final MemoryModelDeclarationInfo mmdi = getMemoryModelDeclarationInfo(decl);
		return mmdi.constructIdentifierExpression(loc);
	}

	private VariableLHS getMemoryModelFeatureLhs(final ILocation loc, final MemoryModelDeclarations decl) {
		requireMemoryModelFeature(decl);
		final MemoryModelDeclarationInfo mmdi = getMemoryModelDeclarationInfo(decl);
		return mmdi.constructVariableLHS(loc);
	}

	public Collection<Statement> getChecksForFreeCall(final ILocation loc, final RValue pointerToBeFreed) {
		assert pointerToBeFreed.getCType().getUnderlyingType() instanceof CPointer;

		final Expression nr0 = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final Expression valid = getValidArray(loc);
		final Expression addrOffset = getPointerOffset(pointerToBeFreed.getValue(), loc);
		final Expression addrBase = getPointerBaseAddress(pointerToBeFreed.getValue(), loc);
		final Expression[] idcFree = new Expression[] { addrBase };

		final Collection<Statement> result = new ArrayList<>();

		if (mSettings.checkIfFreedPointerIsValid()) {
			/*
			 * creating the specification according to C99:7.20.3.2-2: The free function causes the space pointed to by
			 * ptr to be deallocated, that is, made available for further allocation. If ptr is a null pointer, no
			 * action occurs. Otherwise, if the argument does not match a pointer earlier returned by the calloc,
			 * malloc, or realloc function, or if the space has been deallocated by a call to free or realloc, the
			 * behavior is undefined.
			 */
			final Check check = new Check(Spec.MEMORY_FREE);
			{
				// assert (~addr!offset == 0);
				final AssertStatement offsetZero = new AssertStatement(loc,
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, addrOffset, nr0));
				check.annotate(offsetZero);
				result.add(offsetZero);
			}

			{
				// assert (~addr!base < #StackHeapBarrier);
				final Expression inHeapArea = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
						IASTBinaryExpression.op_lessThan, getPointerBaseAddress(pointerToBeFreed.getValue(), loc),
						mExpressionTranslation.getCTypeOfPointerComponents(), getStackHeapBarrier(loc),
						mExpressionTranslation.getCTypeOfPointerComponents());
				final AssertStatement assertInHeapArea = new AssertStatement(loc, inHeapArea);
				check.annotate(assertInHeapArea);
				result.add(assertInHeapArea);
			}

			{
				// ~addr!base == 0
				final Expression ptrBaseZero = mTypeSizes.constructLiteralForIntegerType(loc,
						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
				final Expression isNullPtr =
						ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, addrBase, ptrBaseZero);

				// requires ~addr!base == 0 || #valid[~addr!base];
				final Expression addrIsValid = mBooleanArrayHelper
						.compareWithTrue(ExpressionFactory.constructNestedArrayAccessExpression(loc, valid, idcFree));
				final AssertStatement baseValid = new AssertStatement(loc,
						ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, isNullPtr, addrIsValid));
				check.annotate(baseValid);
				result.add(baseValid);
			}
		}

		return result;
	}

	/**
	 * Returns a call to our internal Ultimate.dealloc procedure. Also notifies the relevant handlers (MemoryHandler,
	 * FunctionHandler) about the call.
	 *
	 * Note that Ultimate.dealloc does not make check if the deallocated memory is #valid, this must be done outside of
	 * this procedure if we are translating a call to C's <code>free(p)</code> function for example.
	 */
	public CallStatement getDeallocCall(final LRValue lrVal, final ILocation loc) {
		assert lrVal instanceof RValue || lrVal instanceof LocalLValue;
		requireMemoryModelFeature(MemoryModelDeclarations.ULTIMATE_DEALLOC);
		// Further checks are done in the precondition of ~free()!
		return StatementFactory.constructCallStatement(loc, false, new VariableLHS[0],
				MemoryModelDeclarations.ULTIMATE_DEALLOC.getName(), new Expression[] { lrVal.getValue() });
	}

	public CallStatement getUltimateMemAllocCall(final LocalLValue resultPointer, final ILocation loc,
			final MemoryArea memArea) {
		return getUltimateMemAllocCall(calculateSizeOf(loc, resultPointer.getCType()),
				(VariableLHS) resultPointer.getLhs(), loc, memArea);
	}

	public CallStatement getUltimateMemAllocCall(final Expression size, final VariableLHS returnedValue,
			final ILocation loc, final MemoryArea memArea) {

		final MemoryModelDeclarations alloc = memArea.getMemoryModelDeclaration();
		requireMemoryModelFeature(alloc);
		final Expression wrappedSize = mExpressionTranslation.applyWraparound(loc, mTypeSizes.getSizeT(), size);
		final CallStatement result = StatementFactory.constructCallStatement(loc, false,
				new VariableLHS[] { returnedValue }, alloc.getName(), new Expression[] { wrappedSize });

		mProcedureManager.registerProcedure(alloc.getName());
		return result;
	}

	/**
	 * Call for procedure that can allocate memory during the initialization. See
	 * {@link MemoryModelDeclarations#ULTIMATE_ALLOC_INIT}.
	 */
	public CallStatement getUltimateMemAllocInitCall(final Expression size, final RValue addressRValue,
			final ILocation loc) {
		requireMemoryModelFeature(MemoryModelDeclarations.ULTIMATE_ALLOC_INIT);
		final CallStatement result = StatementFactory.constructCallStatement(loc, false, new VariableLHS[] {},
				MemoryModelDeclarations.ULTIMATE_ALLOC_INIT.getName(),
				new Expression[] { size, addressRValue.getValue() });
		mProcedureManager.registerProcedure(MemoryModelDeclarations.ULTIMATE_ALLOC_INIT.getName());
		return result;
	}

	/**
	 * Call for procedure that can allocate memory during the initialization. See
	 * {@link MemoryModelDeclarations#ULTIMATE_ALLOC_INIT}.
	 *
	 * @param cType
	 *            type of the object for which we allocate memory (unlike {@link MemoryHandler#getUltimateMemAllocCall}
	 *            which takes a pointer to the object for which allocate.
	 */
	public Pair<RValue, CallStatement> getUltimateMemAllocInitCall(final ILocation actualLoc, final CType cType) {
		final BigInteger ptrBase = BigInteger.valueOf(mFixedAddressCounter);
		final Expression addressExpression =
				mExpressionTranslation.constructPointerForIntegerValues(actualLoc, ptrBase, BigInteger.ZERO);
		final RValue addressRValue = new RValue(addressExpression, cType);
		final RValue ptrBaseRValue = new RValue(
				mTypeSizes.constructLiteralForIntegerType(actualLoc,
						mExpressionTranslation.getCTypeOfPointerComponents(), ptrBase),
				mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression size = mTypeSizeAndOffsetComputer.constructBytesizeExpression(actualLoc, cType);
		final CallStatement ultimateAllocCall = getUltimateMemAllocInitCall(size, ptrBaseRValue, actualLoc);
		mFixedAddressCounter++;
		return new Pair<>(addressRValue, ultimateAllocCall);
	}

	/**
	 * Generates a call of the read procedure and writes the returned value to a temp variable, returned in the
	 * expression of the returned ResultExpression. Note that we only read simple types from the heap -- when reading
	 * e.g. an array, we have to make readCalls for each cell.
	 *
	 * @param tPointer
	 *            the address to read from.
	 * @param pointerCType
	 *            the CType of the pointer in tPointer
	 *
	 * @return all declarations and statements required to perform the read, plus an identifierExpression holding the
	 *         read value.
	 */
	// 2015-10
	public ExpressionResult getReadCall(final Expression address, final CType resultType) {
		return getReadCall(address, resultType, false);
	}

	public ExpressionResult getReadCall(final Expression address, final CType resultType, final boolean unchecked) {
		final ILocation loc = address.getLocation();
		final ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MEMREAD);
		resultBuilder.addAuxVarWithDeclaration(auxvar);
		final VariableLHS[] lhss = new VariableLHS[] { auxvar.getLhs() };
		final CallStatement call = StatementFactory.constructCallStatement(loc, false, lhss,
				determineReadProcedure(resultType, unchecked, loc),
				new Expression[] { address, calculateSizeOf(loc, resultType) });
		resultBuilder.addStatement(call);
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder);
		// TODO Frank 2022-12-16: We should add an in-range assumption here, but this could be problematic if we cast
		// e.g. unsigned to signed pointers and read from them
		// mExpressionTranslation.addAssumeValueInRangeStatements(loc, auxvar.getExp(), resultType, resultBuilder);
		resultBuilder.setLrValue(new RValue(auxvar.getExp(), resultType));
		return resultBuilder.build();
	}

	private String determineReadProcedure(final CType resultType, final boolean unchecked, final ILocation loc)
			throws AssertionError {
		final CType ut = resultType.getUnderlyingType();
		if (ut instanceof CPrimitive) {
			final CPrimitive cp = (CPrimitive) ut;
			checkFloatOnHeapSupport(loc, cp);
			mRequiredMemoryModelFeatures.reportDataOnHeapRequired(cp.getType());
			return determineReadProcedureForPrimitive(cp.getType(), unchecked);
		}
		if (ut instanceof CPointer) {
			mRequiredMemoryModelFeatures.reportPointerOnHeapRequired();
			return determineReadProcedureForPointer(unchecked);
		}
		if (ut instanceof CArray) {
			// we assume it is an Array on Heap
			// assert main.cHandler.isHeapVar(((IdentifierExpression) lrVal.getValue()).getIdentifier());
			// but it may not only be on heap, because it is addressoffed, but also because it is inside
			// a struct that is addressoffed..
			mRequiredMemoryModelFeatures.reportPointerOnHeapRequired();
			return determineReadProcedureForPointer(unchecked);
		}
		if (ut instanceof CEnum) {
			// enum is treated like an int
			mRequiredMemoryModelFeatures.reportDataOnHeapRequired(CPrimitives.INT);
			return determineReadProcedureForPrimitive(CPrimitives.INT, unchecked);
		}
		throw new UnsupportedOperationException("unsupported type " + ut);
	}

	private String determineReadProcedureForPointer(final boolean unchecked) {
		if (unchecked) {
			mRequiredMemoryModelFeatures.reportPointerUncheckedReadRequired();
			return mMemoryModel.getUncheckedReadPointerProcedureName();
		}
		mRequiredMemoryModelFeatures.reportPointerOnHeapRequired();
		return mMemoryModel.getReadPointerProcedureName();
	}

	private String determineReadProcedureForPrimitive(final CPrimitives prim, final boolean unchecked) {
		if (unchecked) {
			mRequiredMemoryModelFeatures.reportUncheckedReadRequired(prim);
			return mMemoryModel.getUncheckedReadProcedureName(prim);
		}
		return mMemoryModel.getReadProcedureName(prim);
	}

	/**
	 * Generates a procedure call to writeT(val, ptr), writing val to the according memory array. (for the C-methode the
	 * argument order is value, target, for this method it's the other way around)
	 *
	 * @param hlv
	 *            the HeapLvalue containing the address to write to
	 * @param isStaticInitialization
	 *            If the write call is used during static initialization of global variables, we can use the unchecked
	 *            methods and omit various specifications.
	 * @param rval
	 *            the value to write.
	 *
	 * @return the required Statements to perform the write.
	 */
	public List<Statement> getWriteCall(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CType valueType, final boolean isStaticInitialization) {
		final CType realValueType = valueType.getUnderlyingType();

		final HeapWriteMode writeMode =
				isStaticInitialization ? HeapWriteMode.STORE_UNCHECKED : HeapWriteMode.STORE_CHECKED;
		return getWriteCall(loc, hlv, value, realValueType, writeMode);
	}

	private List<Statement> getWriteCall(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CType valueType, final HeapWriteMode writeMode) {
		final CType realValueType = valueType.getUnderlyingType();

		if (realValueType instanceof CPrimitive) {
			return getWriteCallPrimitive(loc, hlv, value, (CPrimitive) realValueType, writeMode);
		} else if (realValueType instanceof CEnum) {
			return getWriteCallEnum(loc, hlv, value, writeMode);
		} else if (realValueType instanceof CPointer) {
			return getWriteCallPointer(loc, hlv, value, writeMode);
		} else if (realValueType instanceof CStructOrUnion) {
			return getWriteCallStruct(loc, hlv, value, (CStructOrUnion) realValueType, writeMode);
		} else if (realValueType instanceof CArray) {
			return getWriteCallArray(loc, hlv, value, (CArray) realValueType, writeMode);
		} else {
			throw new UnsupportedSyntaxException(loc, "we don't recognize this type: " + realValueType);
		}
	}

	/**
	 * Like {@link #getWriteCall(ILocation, HeapLValue, Expression, CType, boolean)}, but working under the assumption
	 * that the to-be-written heap cells are uninitialized so far. Thus we can use "select-constraints" instead of
	 * "store-constraints" for the heap array.
	 *
	 * @param loc
	 * @param hlv
	 * @param value
	 * @param valueType
	 * @param omit
	 * @param hook
	 * @return
	 */
	public List<Statement> getInitCall(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CType valueType, final IASTNode hook) {
		final CType realValueType = valueType.getUnderlyingType();
		return getWriteCall(loc, hlv, value, realValueType, HeapWriteMode.SELECT);
	}

	/**
	 * Takes a pointer Expression and returns the pointers base address. If it is already given as a struct, then the
	 * first field is returned, otherwise a StructAccessExpression pointer!base is returned.
	 *
	 * @param pointer
	 */
	public static Expression getPointerBaseAddress(final Expression pointer, final ILocation loc) {
		if (pointer instanceof StructConstructor) {
			return ((StructConstructor) pointer).getFieldValues()[0];
		}
		return ExpressionFactory.constructStructAccessExpression(loc, pointer, SFO.POINTER_BASE);
	}

	/**
	 * Takes a pointer Expression and returns the pointers base address. If it is already given as a struct, then the
	 * second field is returned, otherwise a StructAccessExpression pointer!offset is returned.
	 *
	 * @param pointer
	 */
	public static Expression getPointerOffset(final Expression pointer, final ILocation loc) {
		if (pointer instanceof StructConstructor) {
			return ((StructConstructor) pointer).getFieldValues()[1];
		}
		return ExpressionFactory.constructStructAccessExpression(loc, pointer, SFO.POINTER_OFFSET);
	}

	public static StructConstructor constructPointerFromBaseAndOffset(final Expression base, final Expression offset,
			final ILocation loc) {
		return ExpressionFactory.constructStructConstructor(loc, new String[] { SFO.POINTER_BASE, SFO.POINTER_OFFSET },
				new Expression[] { base, offset });
	}

	/**
	 * Takes a loop or function body and inserts mallocs and frees for all the identifiers in this.mallocedAuxPointers
	 *
	 * Note that this returns a statement block that is like the given block but with added statement in front
	 * <b>and</b>in the back!
	 */
	public List<Statement> insertMallocs(final List<Statement> block) {
		final List<Statement> mallocs = new ArrayList<>();
		for (final LocalLValueILocationPair llvp : mVariablesToBeMalloced.currentScopeKeys()) {
			mallocs.add(this.getUltimateMemAllocCall(llvp.llv, llvp.loc, MemoryArea.STACK));
		}
		final List<Statement> frees = new ArrayList<>();
		for (final LocalLValueILocationPair llvp : mVariablesToBeFreed.currentScopeKeys()) {
			// frees are inserted in handleReturnStm
			frees.add(getDeallocCall(llvp.llv, llvp.loc));
			frees.add(new HavocStatement(llvp.loc, new VariableLHS[] { (VariableLHS) llvp.llv.getLhs() }));
		}
		final List<Statement> newBlockAL = new ArrayList<>();
		newBlockAL.addAll(mallocs);
		newBlockAL.addAll(block);
		newBlockAL.addAll(frees);
		return newBlockAL;
	}

	public void addVariableToBeMalloced(final LocalLValueILocationPair llvp) {
		mVariablesToBeMalloced.put(llvp, mVariablesToBeMalloced.getActiveScopeNum());
	}

	public void addVariableToBeFreed(final LocalLValueILocationPair llvp) {
		mVariablesToBeFreed.put(llvp, mVariablesToBeFreed.getActiveScopeNum());
	}

	public Map<LocalLValueILocationPair, Integer> getVariablesToBeFreed() {
		return Collections.unmodifiableMap(mVariablesToBeFreed);
	}

	public IBooleanArrayHelper getBooleanArrayHelper() {
		return mBooleanArrayHelper;
	}

	/**
	 * Add or subtract a Pointer and an integer. Use this method only if you are sure that the type of the integer is
	 * the same as the type that we use for our pointer components. Otherwise, use the method below.
	 *
	 * @param operator
	 *            Either plus or minus.
	 * @param integer
	 * @param valueType
	 *            The value type the pointer points to (we need it because we have to multiply with its size)
	 * @return a pointer of the form: {base: ptr.base, offset: ptr.offset + integer * sizeof(valueType)}
	 */
	public Expression doPointerArithmetic(final int operator, final ILocation loc, final Expression ptrAddress,
			final RValue integer, final CType valueType) {
		if (mTypeSizes.getSize(((CPrimitive) integer.getCType().getUnderlyingType()).getType()) != mTypeSizes
				.getSize(mExpressionTranslation.getCTypeOfPointerComponents().getType())) {
			throw new UnsupportedOperationException("not yet implemented, conversion is needed");
		}
		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(ptrAddress, loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(ptrAddress, loc);
		final Expression timesSizeOf = multiplyWithSizeOfAnotherType(loc, valueType, integer.getValue(),
				mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, operator, pointerOffset,
				mExpressionTranslation.getCTypeOfPointerComponents(), timesSizeOf,
				mExpressionTranslation.getCTypeOfPointerComponents());
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
		return newPointer;
	}

	/**
	 * Like {@link #doPointerArithmetic(int, ILocation, Expression, RValue, CType)} but additionally the integer operand
	 * is converted to the same type that we use to represent pointer components. As a consequence we have to return an
	 * ExpressionResult.
	 */
	public ExpressionResult doPointerArithmeticWithConversion(final int operator, final ILocation loc,
			final Expression ptrAddress, final RValue integer, final CType valueType) {
		final ExpressionResult eres = mExpressionTranslation.convertIntToInt(loc, new ExpressionResult(integer),
				mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression resultExpression =
				doPointerArithmetic(operator, loc, ptrAddress, (RValue) eres.getLrValue(), valueType);
		final RValue newRValue = new RValue(resultExpression, mExpressionTranslation.getCTypeOfPointerComponents());
		return new ExpressionResultBuilder().addAllExceptLrValue(eres).setLrValue(newRValue).build();
	}

	/**
	 * Multiply an integerExpresion with the size of another type.
	 *
	 * @param integerExpresionType
	 *            {@link CType} whose translation is the Boogie type of integerExpression and the result.
	 *
	 * @return An {@link Expression} that represents <i>integerExpression * sizeof(valueType)</i>
	 */
	public Expression multiplyWithSizeOfAnotherType(final ILocation loc, final CType valueType,
			final Expression integerExpression, final CPrimitive integerExpresionType) {
		final Expression timesSizeOf;
		timesSizeOf = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
				integerExpression, integerExpresionType, calculateSizeOf(loc, valueType), integerExpresionType);
		return timesSizeOf;
	}

	public void beginScope() {
		mVariablesToBeMalloced.beginScope();
		mVariablesToBeFreed.beginScope();
	}

	public void endScope() {
		mVariablesToBeMalloced.endScope();
		mVariablesToBeFreed.endScope();
	}

	public IdentifierExpression getPthreadForkCount(final ILocation loc) {
		final BoogieType counterType = mTypeHandler.getBoogieTypeForCType(getThreadIdType());
		return ExpressionFactory.constructIdentifierExpression(loc, counterType, SFO.ULTIMATE_FORK_COUNT,
				new DeclarationInformation(StorageClass.GLOBAL, null));
	}

	public Expression constructMutexArrayIdentifierExpression(final ILocation loc) {
		requireMemoryModelFeature(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX);
		final BoogieArrayType boogieType =
				BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() },
						(BoogieType) mBooleanArrayHelper.constructBoolReplacementType().getBoogieType());
		return ExpressionFactory.constructIdentifierExpression(loc, boogieType, SFO.ULTIMATE_PTHREADS_MUTEX,
				new DeclarationInformation(StorageClass.GLOBAL, null));
	}

	public AssignmentStatement constructMutexArrayAssignment(final ILocation loc, final Expression index,
			final boolean mutexLocked) {
		final BoogieArrayType boogieType =
				BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() },
						(BoogieType) getBooleanArrayHelper().constructBoolReplacementType().getBoogieType());
		final AssignmentStatement as = MemoryHandler.constructOneDimensionalArrayUpdate(loc, index,
				new VariableLHS(loc, boogieType, SFO.ULTIMATE_PTHREADS_MUTEX,
						new DeclarationInformation(StorageClass.GLOBAL, null)),
				getBooleanArrayHelper().constructValue(mutexLocked));
		return as;
	}

	public Expression constructRwLockArrayIdentifierExpression(final ILocation loc) {
		requireMemoryModelFeature(MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK);
		final BoogieArrayType boogieType =
				BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() },
						mTypeHandler.getBoogieTypeForCType(getRwLockCounterType()));
		return ExpressionFactory.constructIdentifierExpression(loc, boogieType, SFO.ULTIMATE_PTHREADS_RWLOCK,
				new DeclarationInformation(StorageClass.GLOBAL, null));
	}

	public void requireMemoryModelFeature(final MemoryModelDeclarations mmDecl) {
		mRequiredMemoryModelFeatures.require(mmDecl);

		MemoryModelDeclarationInfo mmdInfo = mMemoryModelDeclarationInfos.get(mmDecl);
		if (mmdInfo == null) {
			mmdInfo = constructMemoryModelDeclarationInfo(mmDecl);
			mMemoryModelDeclarationInfos.put(mmDecl, mmdInfo);
		}
	}

	/**
	 * If the method returns true, the argument is a literal that represents the NULL pointer. If the method returns
	 * false we don't know if the argument is equivalent to the NULL pointer. This method is not very reliable, use with
	 * caution or improve this method.
	 */
	public boolean isNullPointerLiteral(final Expression expr) {
		if (expr instanceof StructConstructor) {
			final StructConstructor sc = (StructConstructor) expr;
			final Expression[] fieldValues = sc.getFieldValues();
			if (fieldValues.length == 2) {
				final BigInteger fst = mTypeSizes.extractIntegerValue(fieldValues[0], new CPrimitive(CPrimitives.LONG));
				final BigInteger snd = mTypeSizes.extractIntegerValue(fieldValues[1], new CPrimitive(CPrimitives.LONG));
				if (BigInteger.ZERO.equals(fst) && BigInteger.ZERO.equals(snd)) {
					return true;
				}
			}
		}
		final BigInteger integerValue = mTypeSizes.extractIntegerValue(expr, new CPrimitive(CPrimitives.LONG));
		if (BigInteger.ZERO.equals(integerValue)) {
			return true;
		}
		return false;
	}

	private MemoryModelDeclarationInfo getMemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
		final MemoryModelDeclarationInfo result = mMemoryModelDeclarationInfos.get(mmd);
		if (result == null) {
			throw new AssertionError("call  requireMemoryModelFeature first!");
		}
		return result;
	}

	private BaseMemoryModel getMemoryModel(final boolean bitvectorTranslation, final MemoryModel memoryModelPreference)
			throws AssertionError {
		final BaseMemoryModel memoryModel;
		if (bitvectorTranslation) {
			switch (memoryModelPreference) {
			case HoenickeLindenmann_1ByteResolution:
			case HoenickeLindenmann_2ByteResolution:
			case HoenickeLindenmann_4ByteResolution:
			case HoenickeLindenmann_8ByteResolution:
				memoryModel = new MemoryModel_SingleBitprecise(memoryModelPreference.getByteSize(), mTypeSizes,
						(TypeHandler) mTypeHandler, mExpressionTranslation);
				break;
			case HoenickeLindenmann_Original:
				memoryModel = new MemoryModel_MultiBitprecise(mTypeSizes, mTypeHandler, mExpressionTranslation);
				break;
			default:
				throw new AssertionError("unknown value");
			}
		} else {
			switch (memoryModelPreference) {
			case HoenickeLindenmann_Original:
				memoryModel = new MemoryModel_Unbounded(mTypeSizes, mTypeHandler, mExpressionTranslation);
				break;
			case HoenickeLindenmann_1ByteResolution:
			case HoenickeLindenmann_2ByteResolution:
			case HoenickeLindenmann_4ByteResolution:
			case HoenickeLindenmann_8ByteResolution:
				throw new UnsupportedOperationException(
						"Memory model " + memoryModelPreference + " only available in bitprecise translation");
			default:
				throw new AssertionError("unknown value");
			}
		}
		return memoryModel;
	}

	/**
	 * Check that there is no procedure declaration (i.e. a Procedure without a body) in the given set of Declarations.
	 *
	 * @param decl
	 * @return
	 */
	private static boolean assertContainsNodeProcedureDeclarations(final Collection<Declaration> decl) {
		for (final Declaration d : decl) {
			if (d instanceof Procedure && ((Procedure) d).getBody() == null) {
				assert false : "found a procedure declaration";
				return false;
			}
		}
		return true;
	}

	private VariableDeclaration constuctLengthArrayDeclaration() {
		// var #length : [int]int;
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ASTType pointerComponentType =
				mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents());
		final BoogieType boogieType =
				BoogieType.createArrayType(0, new BoogieType[] { (BoogieType) pointerComponentType.getBoogieType() },
						(BoogieType) pointerComponentType.getBoogieType());
		final ASTType lengthType = new ArrayType(ignoreLoc, boogieType, new String[0],
				new ASTType[] { pointerComponentType }, pointerComponentType);
		final VarList vlL = new VarList(ignoreLoc, new String[] { SFO.LENGTH }, lengthType);
		return new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] { vlL });
	}

	private VariableDeclaration constructValidArrayDeclaration() {
		// var #valid : [int]bool;
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ASTType pointerComponentType =
				mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents());
		final BoogieType boogieType =
				BoogieType.createArrayType(0, new BoogieType[] { (BoogieType) pointerComponentType.getBoogieType() },
						(BoogieType) mBooleanArrayHelper.constructBoolReplacementType().getBoogieType());
		final ASTType validType = new ArrayType(ignoreLoc, boogieType, new String[0],
				new ASTType[] { pointerComponentType }, mBooleanArrayHelper.constructBoolReplacementType());
		final VarList vlV =
				new VarList(ignoreLoc, new String[] { MemoryModelDeclarations.ULTIMATE_VALID.getName() }, validType);
		return new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] { vlV });
	}

	/**
	 * TODO 2019-12-26 Matthias: Our verifier does probably not support Boogie constants soundly as a workaround, we
	 * construct a variable instead.
	 */
	private VariableDeclaration constructStackHeapBarrierConstant() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final VariableDeclaration result = new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
		return result;
	}

	private List<Declaration> declareUltimateMeminit(final CHandler main,
			final Collection<HeapDataArray> heapDataArrays) {
		final ArrayList<Declaration> decls = new ArrayList<>();
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final String inParamPtr = "#ptr";
		final String inParamAmountOfFields = "#amountOfFields";
		final String inParamSizeOfFields = "#sizeOfFields";
		final String inParamProduct = "#product";
		final String procName = MemoryModelDeclarations.ULTIMATE_MEMINIT.getName();

		final VarList[] inParams;
		final VarList[] outParams;
		final VarList inParamPtrVl =
				new VarList(ignoreLoc, new String[] { inParamPtr }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList inParamAmountOfFieldsVl = new VarList(ignoreLoc, new String[] { inParamAmountOfFields },
				mTypeHandler.cType2AstType(ignoreLoc, mTypeSizeAndOffsetComputer.getSizeT()));
		final VarList inParamSizeOfFieldsVl = new VarList(ignoreLoc, new String[] { inParamSizeOfFields },
				mTypeHandler.cType2AstType(ignoreLoc, mTypeSizeAndOffsetComputer.getSizeT()));
		final VarList inParamProductVl = new VarList(ignoreLoc, new String[] { inParamProduct },
				mTypeHandler.cType2AstType(ignoreLoc, mTypeSizeAndOffsetComputer.getSizeT()));

		inParams = new VarList[] { inParamPtrVl, inParamAmountOfFieldsVl, inParamSizeOfFieldsVl, inParamProductVl };
		outParams = new VarList[] {};

		final Procedure memCpyProcDecl = new Procedure(ignoreLoc, new Attribute[0], procName, new String[0], inParams,
				outParams, new Specification[0], null);

		mProcedureManager.beginCustomProcedure(main, ignoreLoc, procName, memCpyProcDecl);

		final List<VariableDeclaration> decl = new ArrayList<>();
		final List<Statement> stmt = new ArrayList<>();
		if (mSettings.useConstantArrays()) {

			final IdentifierExpression pointerIdExpr =
					ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(),
							inParamPtr, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));
			final HeapLValue hlv = LRValueFactory.constructHeapLValue(mTypeHandler, pointerIdExpr,
					new CPointer(new CPrimitive(CPrimitives.VOID)), null);

			final Set<CType> cPrimitivesWithRequiredHeapArray = mRequiredMemoryModelFeatures.getDataOnHeapRequired()
					.stream().map(cPrim -> new CPrimitive(cPrim)).collect(Collectors.toSet());
			stmt.addAll(getInitializationForHeapAtPointer(ignoreLoc, hlv, cPrimitivesWithRequiredHeapArray));

		} else {
			final CPrimitive sizeT = mTypeSizeAndOffsetComputer.getSizeT();
			final AuxVarInfo loopCtrAux = mAuxVarInfoBuilder.constructAuxVarInfo(ignoreLoc, sizeT, SFO.AUXVAR.LOOPCTR);
			decl.add(loopCtrAux.getVarDec());

			final Expression zero = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
					new CPrimitive(CPrimitives.UCHAR), BigInteger.ZERO);
			final List<Statement> loopBody =
					constructMemsetLoopBody(heapDataArrays, loopCtrAux, inParamPtr, zero, procName);

			final IdentifierExpression inParamProductExpr =
					ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
							inParamProduct, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));

			final Expression stepsize;
			if (mMemoryModel instanceof MemoryModel_SingleBitprecise) {
				final int resolution = ((MemoryModel_SingleBitprecise) mMemoryModel).getResolution();
				stepsize = mTypeSizes.constructLiteralForIntegerType(ignoreLoc, sizeT, BigInteger.valueOf(resolution));
			} else {
				final IdentifierExpression inParamSizeOfFieldsExpr = ExpressionFactory.constructIdentifierExpression(
						ignoreLoc, BoogieType.TYPE_INT, inParamSizeOfFields,
						new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));

				stepsize = inParamSizeOfFieldsExpr;
			}

			stmt.addAll(constructCountingLoop(constructBoundExitCondition(inParamProductExpr, loopCtrAux), loopCtrAux,
					stepsize, loopBody));
		}

		final Body procBody = mProcedureManager.constructBody(ignoreLoc,
				decl.toArray(new VariableDeclaration[decl.size()]), stmt.toArray(new Statement[stmt.size()]), procName);

		// add the procedure implementation
		final Procedure memCpyProc = new Procedure(ignoreLoc, new Attribute[0], procName, new String[0], inParams,
				outParams, null, procBody);
		decls.add(memCpyProc);

		mProcedureManager.endCustomProcedure(main, procName);
		return decls;
	}

	/**
	 * Construct a loop condition of the form loopCounterAux < loopBoundVariableExpr
	 *
	 * @param loopBoundVariableExpr
	 * @param loopCounterAux
	 * @return
	 */
	public Expression constructBoundExitCondition(final Expression loopBoundVariableExpr,
			final AuxVarInfo loopCounterAux) {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final Expression condition = mExpressionTranslation.constructBinaryComparisonExpression(ignoreLoc,
				IASTBinaryExpression.op_lessThan, loopCounterAux.getExp(), mTypeSizeAndOffsetComputer.getSizeT(),
				loopBoundVariableExpr, mTypeSizeAndOffsetComputer.getSizeT());
		return condition;
	}

	/**
	 * Construct specification and implementation for our Boogie representation of the strcpy function.
	 *
	 * char *strcpy( char *dest, const char *src );
	 *
	 * @param main
	 * @param heapDataArrays
	 * @return
	 */
	private List<Declaration> declareStrCpy(final CHandler main, final Collection<HeapDataArray> heapDataArrays) {

		final MemoryModelDeclarations strcpyMmDecl = MemoryModelDeclarations.C_STRCPY;
		final List<Declaration> strCpyDecl = new ArrayList<>();
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final VarList inPDest =
				new VarList(ignoreLoc, new String[] { SFO.STRCPY_DEST }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList inPSrc =
				new VarList(ignoreLoc, new String[] { SFO.STRCPY_SRC }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList outP =
				new VarList(ignoreLoc, new String[] { SFO.RES }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList[] inParams = new VarList[] { inPDest, inPSrc };
		final VarList[] outParams = new VarList[] { outP };

		{
			final Procedure strCpyProcDecl = new Procedure(ignoreLoc, new Attribute[0], strcpyMmDecl.getName(),
					new String[0], inParams, outParams, new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, ignoreLoc, strcpyMmDecl.getName(), strCpyProcDecl);
		}

		final List<Declaration> decl = new ArrayList<>();
		final CPrimitive sizeT = mTypeSizeAndOffsetComputer.getSizeT();

		final AuxVarInfo loopCtrAux = mAuxVarInfoBuilder.constructAuxVarInfo(ignoreLoc, sizeT, SFO.AUXVAR.OFFSET);
		decl.add(loopCtrAux.getVarDec());

		final Expression srcId = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogiePointerType(), SFO.STRCPY_SRC,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, strcpyMmDecl.getName()));
		final Expression destId = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogiePointerType(), SFO.STRCPY_DEST,
				new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, strcpyMmDecl.getName()));

		// construct the body of the loop (except for the offset incrementing, that is done by constructCountingLoop
		final List<Statement> loopBody = new ArrayList<>();
		{
			final Expression currentSrc = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, srcId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					new CPrimitive(CPrimitives.CHAR));
			final Expression currentDest = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, destId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					new CPrimitive(CPrimitives.CHAR));

			/*
			 * do pointer validity checks for current pointers (src/dest + offset) (using #valid and #length)
			 *
			 * assert #valid[src!base] == 1; assert src!offset + #t~offset15 * 1 < #length[src!base] && src!offset +
			 * #t~offset15 * 1 >= 0; assert #valid[dest!base] == 1; assert dest!offset + #t~offset15 * 1 <
			 * #length[dest!base] && dest!offset + #t~offset15 * 1 >= 0;
			 */
			{
				final List<Statement> checkSrcPtr = constructMemsafetyChecksForPointerExpression(ignoreLoc, currentSrc);
				loopBody.addAll(checkSrcPtr);

				final List<Statement> checkDestPtr =
						constructMemsafetyChecksForPointerExpression(ignoreLoc, currentDest);
				loopBody.addAll(checkDestPtr);
			}

			/*
			 * check that dest and src do not overlap (that would be undefined behaviour)
			 *
			 * assert src!base != src!base || (dest!offset + #t~offset15 * 1 < src!offset && src!offset + #t~offset15 *
			 * 1 < dest!offset);
			 *
			 * TODO: if and when we want to check for this kind of undefined behavior, we should activate this check
			 */
			final boolean checkForStringCopyOverlapingUndefindeBehaviour = false;
			if (checkForStringCopyOverlapingUndefindeBehaviour) {
				final Expression basesDistinct = ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPNEQ,
						getPointerBaseAddress(currentSrc, ignoreLoc), getPointerBaseAddress(currentSrc, ignoreLoc));
				final Expression destDoesNotReachIntoSrc = ExpressionFactory.newBinaryExpression(ignoreLoc,
						Operator.COMPLT, getPointerOffset(currentDest, ignoreLoc), getPointerOffset(srcId, ignoreLoc));
				final Expression srcDoesNotReachIntoDest = ExpressionFactory.newBinaryExpression(ignoreLoc,
						Operator.COMPLT, getPointerOffset(currentSrc, ignoreLoc), getPointerOffset(destId, ignoreLoc));
				final Expression disjunction = ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.LOGICOR,
						basesDistinct, ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.LOGICAND,
								destDoesNotReachIntoSrc, srcDoesNotReachIntoDest));
				loopBody.add(new AssertStatement(ignoreLoc, disjunction));
			}

			final Expression srcAcc;
			{
				final ExpressionResult srcAccExpRes = this.getReadCall(currentSrc, new CPrimitive(CPrimitives.CHAR));
				srcAcc = srcAccExpRes.getLrValue().getValue();
				loopBody.addAll(srcAccExpRes.getStatements());
				decl.addAll(srcAccExpRes.getDeclarations());
				assert srcAccExpRes.getOverapprs().isEmpty();
			}

			/*
			 * #memory_int[{ base: dest!base, offset: dest!offset + #t~offset * 3 }] := #memory_int[{ base: src!base,
			 * offset: src!offset + #t~offset * 3 }];
			 */
			{
				final List<Statement> writeCall = getWriteCall(
						ignoreLoc, LRValueFactory.constructHeapLValue(mTypeHandler, currentDest,
								new CPrimitive(CPrimitives.CHAR), null),
						srcAcc, new CPrimitive(CPrimitives.CHAR), true);
				loopBody.addAll(writeCall);
			}

			/* if (#memory_int[currentSrc] == 0) { break; } */
			{
				final Expression zero = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
						new CPrimitive(CPrimitives.CHAR), BigInteger.ZERO);
				final Expression exitCondition = mExpressionTranslation.constructBinaryComparisonExpression(ignoreLoc,
						IASTBinaryExpression.op_equals, srcAcc, new CPrimitive(CPrimitives.CHAR), zero,
						new CPrimitive(CPrimitives.CHAR));
				final Statement exitIfNull = new IfStatement(ignoreLoc, exitCondition,
						new Statement[] { new BreakStatement(ignoreLoc) }, new Statement[0]);
				loopBody.add(exitIfNull);
			}
		}

		// loop condition is true (we exit the loop via a conditional break)
		final Expression loopCondition = ExpressionFactory.createBooleanLiteral(ignoreLoc, true);

		final Expression loopCtrIncrement = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
		final List<Statement> loop = constructCountingLoop(loopCondition, loopCtrAux, loopCtrIncrement, loopBody);

		final Body procBody =
				mProcedureManager.constructBody(ignoreLoc, decl.toArray(new VariableDeclaration[decl.size()]),
						loop.toArray(new Statement[loop.size()]), strcpyMmDecl.getName());

		// make the specifications
		final ArrayList<Specification> specs = new ArrayList<>();

		/*
		 * free ensures #res == dest; (this is done instead of a return statement, took this from memcpy/memmove, not
		 * sure why we are not using a return statement)
		 */
		final EnsuresSpecification returnValue = mProcedureManager.constructEnsuresSpecification(ignoreLoc, true,
				ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ,
						ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(),
								SFO.RES,
								new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, strcpyMmDecl.getName())),
						ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(),
								SFO.MEMCPY_DEST,
								new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, strcpyMmDecl.getName()))),
				Collections.emptySet());
		specs.add(returnValue);

		// add the procedure declaration
		mProcedureManager.addSpecificationsToCurrentProcedure(specs);

		// add the procedure implementation
		final Procedure strCpyProc = new Procedure(ignoreLoc, new Attribute[0], strcpyMmDecl.getName(), new String[0],
				inParams, outParams, null, procBody);
		strCpyDecl.add(strCpyProc);

		mProcedureManager.endCustomProcedure(main, strcpyMmDecl.getName());

		return strCpyDecl;
	}

	/**
	 * Construct loop of the following form, where loopBody is a List of statements and the variables loopConterVariable
	 * and loopBoundVariable have the translated type of size_t.
	 *
	 * loopConterVariable := 0; while (condition) { ___loopBody___ loopConterVariable := loopConterVariable + 1; }
	 *
	 * @param condition
	 *            (may depend on
	 * @param loopBody
	 * @param loopCounterVariableId
	 * @return
	 */
	public List<Statement> constructCountingLoop(final Expression condition, final AuxVarInfo loopCounterAux,
			final Expression loopCounterIncrementExpr, final List<Statement> loopBody) {
		final CACSLLocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ArrayList<Statement> stmt = new ArrayList<>();

		// initialize the counter to 0
		final Expression zero = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
				mTypeSizeAndOffsetComputer.getSizeT(), BigInteger.ZERO);
		stmt.add(StatementFactory.constructAssignmentStatement(ignoreLoc,
				new LeftHandSide[] { loopCounterAux.getLhs() }, new Expression[] { zero }));

		final ArrayList<Statement> bodyStmt = new ArrayList<>();
		bodyStmt.addAll(loopBody);

		// increment counter
		final VariableLHS ctrLHS = loopCounterAux.getLhs();
		final Expression counterPlusOne =
				mExpressionTranslation.constructArithmeticExpression(ignoreLoc, IASTBinaryExpression.op_plus,
						loopCounterAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents(),
						loopCounterIncrementExpr, mExpressionTranslation.getCTypeOfPointerComponents());
		bodyStmt.add(StatementFactory.constructAssignmentStatement(ignoreLoc, new LeftHandSide[] { ctrLHS },
				new Expression[] { counterPlusOne }));

		final Statement[] whileBody = bodyStmt.toArray(new Statement[bodyStmt.size()]);

		final WhileStatement whileStm =
				new WhileStatement(ignoreLoc, condition, new LoopInvariantSpecification[0], whileBody);
		stmt.add(whileStm);
		return stmt;
	}

	private ArrayList<Statement> constructMemsetLoopBody(final Collection<HeapDataArray> heapDataArrays,
			final AuxVarInfo loopCtr, final String ptr, final Expression valueExpr,
			final String surroundingProcedureName) {

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ArrayList<Statement> result = new ArrayList<>();

		final IdentifierExpression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(), ptr,
						new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, surroundingProcedureName));

		final Expression currentPtr = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, ptrExpr,
				new RValue(loopCtr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
				new CPrimitive(CPrimitives.VOID));
		for (final HeapDataArray hda : heapDataArrays) {
			final Expression convertedValue;
			ExpressionResult exprRes = new ExpressionResult(new RValue(valueExpr, new CPrimitive(CPrimitives.UCHAR)));
			if (hda.getName().equals(SFO.POINTER)) {
				exprRes = mExpressionTranslation.convertIntToInt(ignoreLoc, exprRes,
						mExpressionTranslation.getCTypeOfPointerComponents());
				final Expression zero = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
				convertedValue = constructPointerFromBaseAndOffset(zero, exprRes.getLrValue().getValue(), ignoreLoc);
			} else if (hda.getName().equals(SFO.REAL)) {
				final CPrimitives primitive = getFloatingCprimitiveThatFitsBest(hda.getSize());
				exprRes = mExpressionTranslation.convertIntToFloat(ignoreLoc, exprRes, new CPrimitive(primitive));
				convertedValue = exprRes.getLrValue().getValue();
			} else {
				// convert to smallest
				final CPrimitives primitive = getCprimitiveThatFitsBest(hda.getSize());
				exprRes = mExpressionTranslation.convertIntToInt(ignoreLoc, exprRes, new CPrimitive(primitive));
				convertedValue = exprRes.getLrValue().getValue();
			}
			final ArrayLHS destAcc = ExpressionFactory.constructNestedArrayLHS(ignoreLoc, hda.getVariableLHS(),
					new Expression[] { currentPtr });

			result.add(StatementFactory.constructAssignmentStatement(ignoreLoc, new LeftHandSide[] { destAcc },
					new Expression[] { convertedValue }));
		}
		return result;
	}

	/**
	 * Returns an CPrimitive which is unsigned, integer and not bool that has the smallest bytesize.
	 */
	private CPrimitives getCprimitiveThatFitsBest(final int byteSize) {
		if (byteSize == 0) {
			// we only have unbounded data types
			return CPrimitives.UCHAR;
		}
		for (final CPrimitives primitive : new CPrimitives[] { CPrimitives.UCHAR, CPrimitives.USHORT, CPrimitives.UINT,
				CPrimitives.ULONG, CPrimitives.ULONGLONG, CPrimitives.UINT128 }) {
			if (mTypeSizes.getSize(primitive) == byteSize) {
				return primitive;
			}
		}
		throw new AssertionError("don't know how to store value on heap");
	}

	/**
	 * Returns a CPrimitive which is floating and non-complex that has the smallest bytesize.
	 */
	private CPrimitives getFloatingCprimitiveThatFitsBest(final int byteSize) {
		if (byteSize == 0) {
			return CPrimitives.FLOAT;
		}
		for (final CPrimitives primitive : new CPrimitives[] { CPrimitives.FLOAT, CPrimitives.DOUBLE,
				CPrimitives.LONGDOUBLE }) {
			if (mTypeSizes.getSize(primitive) == byteSize) {
				return primitive;
			}
		}
		throw new AssertionError("don't know how to store value on heap");
	}

	/**
	 * Construct specification and implementation for our Boogie representation of the memset function defined in
	 * 7.24.6.1 of C11. void *memset(void *s, int c, size_t n);
	 *
	 * @param main
	 * @param heapDataArrays
	 * @return
	 */
	private List<Declaration> declareMemset(final CHandler main, final Collection<HeapDataArray> heapDataArrays) {
		final ArrayList<Declaration> decls = new ArrayList<>();
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final String inParamPtr = "#ptr";
		final String inParamValue = "#value";
		final String inParamAmount = "#amount";
		final String outParamResult = "#res";
		final String procName = MemoryModelDeclarations.C_MEMSET.getName();

		final VarList inParamPtrVl =
				new VarList(ignoreLoc, new String[] { inParamPtr }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList inParamValueVl = new VarList(ignoreLoc, new String[] { inParamValue },
				mTypeHandler.cType2AstType(ignoreLoc, new CPrimitive(CPrimitives.INT)));
		final VarList inParamAmountVl = new VarList(ignoreLoc, new String[] { inParamAmount },
				mTypeHandler.cType2AstType(ignoreLoc, mTypeSizeAndOffsetComputer.getSizeT()));
		final VarList outParamResultVl =
				new VarList(ignoreLoc, new String[] { outParamResult }, mTypeHandler.constructPointerType(ignoreLoc));

		final VarList[] inParams = new VarList[] { inParamPtrVl, inParamValueVl, inParamAmountVl };
		final VarList[] outParams = new VarList[] { outParamResultVl };

		{
			final Procedure procDecl = new Procedure(ignoreLoc, new Attribute[0], procName, new String[0], inParams,
					outParams, new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, ignoreLoc, procName, procDecl);
		}

		final List<VariableDeclaration> decl = new ArrayList<>();
		final CPrimitive sizeT = mTypeSizeAndOffsetComputer.getSizeT();
		final AuxVarInfo loopCtrAux = mAuxVarInfoBuilder.constructAuxVarInfo(ignoreLoc, sizeT, SFO.AUXVAR.LOOPCTR);
		decl.add(loopCtrAux.getVarDec());

		// converted value to unsigned char
		final IdentifierExpression inParamValueExpr = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				(BoogieType) mTypeHandler.cType2AstType(ignoreLoc, new CPrimitive(CPrimitives.INT)).getBoogieType(),
				inParamValue, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));

		final ExpressionResult exprRes =
				new ExpressionResult(new RValue(inParamValueExpr, new CPrimitive(CPrimitives.INT)));
		final ExpressionResult convertedExprRes =
				mExpressionTranslation.convertIntToInt(ignoreLoc, exprRes, new CPrimitive(CPrimitives.UCHAR));
		final Expression convertedValue = convertedExprRes.getLrValue().getValue();

		final List<Statement> loopBody =
				constructMemsetLoopBody(heapDataArrays, loopCtrAux, inParamPtr, convertedValue, procName);

		final Expression one = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
				mTypeSizeAndOffsetComputer.getSizeT(), BigInteger.ONE);
		final IdentifierExpression inParamAmountExprImpl =
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
						inParamAmount, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));

		final List<Statement> stmt = constructCountingLoop(
				constructBoundExitCondition(inParamAmountExprImpl, loopCtrAux), loopCtrAux, one, loopBody);

		final Body procBody = mProcedureManager.constructBody(ignoreLoc,
				decl.toArray(new VariableDeclaration[decl.size()]), stmt.toArray(new Statement[stmt.size()]), procName);

		// make the specifications
		final ArrayList<Specification> specs = new ArrayList<>();

		// add requires #valid[#ptr!base];
		specs.addAll(constructPointerBaseValidityCheck(ignoreLoc, inParamPtr, procName));

		final IdentifierExpression inParamAmountExprDecl =
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
						inParamAmount, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procName));
		// add requires (#size + #ptr!offset <= #length[#ptr!base] && 0 <= #ptr!offset);
		specs.addAll(constructPointerTargetFullyAllocatedCheck(ignoreLoc, inParamAmountExprDecl, inParamPtr, procName));

		// free ensures #res == dest;
		final EnsuresSpecification returnValue = mProcedureManager.constructEnsuresSpecification(ignoreLoc, true,
				ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ,
						ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(),
								outParamResult, new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, procName)),
						ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(),
								inParamPtr, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procName))),
				Collections.emptySet());

		specs.add(returnValue);

		// add the procedure declaration
		mProcedureManager.addSpecificationsToCurrentProcedure(specs);

		// add the procedure implementation
		final Procedure procImpl = new Procedure(ignoreLoc, new Attribute[0], procName, new String[0], inParams,
				outParams, null, procBody);
		decls.add(procImpl);

		mProcedureManager.endCustomProcedure(main, procName);

		return decls;
	}

	private VariableDeclaration constructMemoryArrayDeclaration(final ILocation loc, final String typeName,
			final ASTType valueType) {
		final String arrayName = SFO.MEMORY + "_" + typeName;
		return constructDeclOfPointerIndexedArray(loc, valueType, arrayName);
	}

	private VariableDeclaration constructDeclOfPointerIndexedArray(final ILocation loc, final ASTType valueType,
			final String arrayName) {
		final BoogieArrayType boogieType = BoogieType.createArrayType(0,
				new BoogieType[] { mTypeHandler.getBoogiePointerType() }, (BoogieType) valueType.getBoogieType());
		final ASTType memoryArrayType = new ArrayType(loc, boogieType, new String[0],
				new ASTType[] { mTypeHandler.constructPointerType(loc) }, valueType);
		final VarList varList = new VarList(loc, new String[] { arrayName }, memoryArrayType);
		return new VariableDeclaration(loc, new Attribute[0], new VarList[] { varList });
	}

	private List<Declaration> constructWriteProcedures(final CHandler main, final ILocation loc,
			final Collection<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray) {
		final List<Declaration> result = new ArrayList<>();
		for (final ReadWriteDefinition rda : mMemoryModel.getReadWriteDefinitionForHeapDataArray(heapDataArray,
				mRequiredMemoryModelFeatures)) {
			final Collection<Procedure> writeDeclaration =
					constructWriteProcedure(main, loc, heapDataArrays, heapDataArray, rda);
			result.addAll(writeDeclaration);
		}
		return result;
	}

	private List<Declaration> constructReadProcedures(final CHandler main, final ILocation loc,
			final HeapDataArray heapDataArray) {
		final List<Declaration> result = new ArrayList<>();
		for (final ReadWriteDefinition rda : mMemoryModel.getReadWriteDefinitionForHeapDataArray(heapDataArray,
				mRequiredMemoryModelFeatures)) {
			if (rda.alsoUncheckedRead()) {
				result.addAll(constructSingleReadProcedure(main, loc, heapDataArray, rda, true));
			}
			result.addAll(constructSingleReadProcedure(main, loc, heapDataArray, rda, false));
		}
		return result;
	}

	private VariableDeclaration declarePthreadsForkCount(final ILocation loc) {
		final ASTType counterType = mTypeHandler.cType2AstType(loc, getThreadIdType());
		final VarList varList = new VarList(loc, new String[] { SFO.ULTIMATE_FORK_COUNT }, counterType);
		return new VariableDeclaration(loc, new Attribute[0], new VarList[] { varList });
	}

	public CPrimitive getThreadIdType() {
		return new CPrimitive(CPrimitives.INT);
	}

	private VariableDeclaration declarePThreadsMutexArray(final ILocation loc) {
		final String arrayName = SFO.ULTIMATE_PTHREADS_MUTEX;
		return constructDeclOfPointerIndexedArray(loc, mBooleanArrayHelper.constructBoolReplacementType(), arrayName);
	}

	private static CPrimitive getRwLockCounterType() {
		return new CPrimitive(CPrimitives.SCHAR);
	}

	private VariableDeclaration declarePthreadRwLock(final ILocation loc) {
		return constructDeclOfPointerIndexedArray(loc, mTypeHandler.cType2AstType(loc, getRwLockCounterType()),
				SFO.ULTIMATE_PTHREADS_RWLOCK);
	}

	/**
	 * Note that we do not return a Procedure declaration here anymore because procedure declarations are handled by the
	 * FunctionHandler (DD: Do you mean {@link ProcedureManager} ??) directly. So the return value will be an empty set,
	 * or perhaps in the future an implementation, should we ever want one.
	 *
	 * @param main
	 * @param loc
	 * @param heapDataArrays
	 * @param heapDataArray
	 * @param rda
	 * @return
	 */
	private Collection<Procedure> constructWriteProcedure(final CHandler main, final ILocation loc,
			final Collection<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray,
			final ReadWriteDefinition rda) {
		if (rda.alsoUncheckedWrite()) {
			constructSingleWriteProcedure(main, loc, heapDataArrays, heapDataArray, rda, HeapWriteMode.STORE_UNCHECKED);
		}
		if (rda.alsoInit()) {
			constructSingleWriteProcedure(main, loc, heapDataArrays, heapDataArray, rda, HeapWriteMode.SELECT);
		}
		constructSingleWriteProcedure(main, loc, heapDataArrays, heapDataArray, rda, HeapWriteMode.STORE_CHECKED);
		return Collections.emptySet();
	}

	private void constructSingleWriteProcedure(final CHandler main, final ILocation loc,
			final Collection<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray,
			final ReadWriteDefinition rda, final HeapWriteMode writeMode) {
		final String inPtr = "#ptr";
		final String writtenTypeSize = "#sizeOfWrittenType";
		final ASTType valueAstType = rda.getASTType();

		// create procedure signature
		final String procName;
		switch (writeMode) {
		case SELECT:
			procName = rda.getInitWriteProcedureName();
			break;
		case STORE_CHECKED:
			procName = rda.getWriteProcedureName();
			break;
		case STORE_UNCHECKED:
			procName = rda.getUncheckedWriteProcedureName();
			break;
		default:
			throw new AssertionError("todo: update according to new enum contents");
		}

		final IdentifierExpression inPtrExp =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), inPtr,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procName));

		final ASTType sizetType = mTypeHandler.cType2AstType(loc, mTypeSizeAndOffsetComputer.getSizeT());
		final VarList[] inWrite = new VarList[] { new VarList(loc, new String[] { "#value" }, valueAstType),
				new VarList(loc, new String[] { inPtr }, mTypeHandler.constructPointerType(loc)),
				new VarList(loc, new String[] { writtenTypeSize }, sizetType) };

		final Procedure proc = new Procedure(loc, new Attribute[0], procName, new String[0], inWrite, new VarList[0],
				new Specification[0], null);
		mProcedureManager.beginCustomProcedure(main, loc, procName, proc);

		// specification for memory writes
		final ArrayList<Specification> swrite = new ArrayList<>();
		if (writeMode == HeapWriteMode.STORE_CHECKED) {
			swrite.addAll(constructPointerBaseValidityCheck(loc, inPtr, procName));

			final Expression sizeWrite = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogieTypeForPointerComponents(), writtenTypeSize,
					new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procName));
			swrite.addAll(constructPointerTargetFullyAllocatedCheck(loc, sizeWrite, inPtr, procName));
		}

		final boolean floating2bitvectorTransformationNeeded = mMemoryModel instanceof MemoryModel_SingleBitprecise
				&& rda.getCPrimitiveCategory().contains(CPrimitiveCategory.FLOATTYPE);

		final Expression nonFPBVReturnValue = ExpressionFactory.constructIdentifierExpression(loc,
				mTypeHandler.getBoogieTypeForBoogieASTType(valueAstType), "#value",
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procName));
		final CPrimitives cprimitive;
		final Expression returnValue;
		if (floating2bitvectorTransformationNeeded) {
			cprimitive = rda.getPrimitives().iterator().next();
			if (mSettings.useFpToIeeeBvExtension()) {
				returnValue = mExpressionTranslation.transformFloatToBitvector(loc, nonFPBVReturnValue, cprimitive);
			} else {
				returnValue = ExpressionFactory.constructIdentifierExpression(loc,
						mTypeHandler.getBoogieTypeForBoogieASTType(valueAstType), "#valueAsBitvector",
						new DeclarationInformation(StorageClass.QUANTIFIED, null));
			}
		} else {
			cprimitive = null;
			returnValue = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(valueAstType), "#value",
					new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procName));
		}

		final boolean useSelectInsteadOfStore = writeMode == HeapWriteMode.SELECT;

		final List<Expression> indices = new ArrayList<>();
		final List<Expression> values = new ArrayList<>();
		if (rda.getBytesize() == heapDataArray.getSize()) {
			indices.add(inPtrExp);
			values.add(returnValue);
		} else if (rda.getBytesize() < heapDataArray.getSize()) {
			final Function<Expression, Expression> valueExtension =
					x -> mExpressionTranslation.signExtend(loc, x, rda.getBytesize() * 8, heapDataArray.getSize() * 8);
			indices.add(inPtrExp);
			values.add(valueExtension.apply(returnValue));
		} else {
			assert rda.getBytesize() % heapDataArray.getSize() == 0 : "incompatible sizes";
			for (int i = 0; i < rda.getBytesize() / heapDataArray.getSize(); i++) {
				final Function<Expression, Expression> extractBits;
				final int currentI = i;
				extractBits = x -> mExpressionTranslation.extractBits(loc, x,
						heapDataArray.getSize() * (currentI + 1) * 8, heapDataArray.getSize() * currentI * 8);
				if (i == 0) {
					indices.add(inPtrExp);
					values.add(extractBits.apply(returnValue));

				} else {
					final BigInteger additionalOffset = BigInteger.valueOf(i * heapDataArray.getSize());
					final Function<Expression, Expression> pointerAddition =
							x -> addIntegerConstantToPointer(loc, x, additionalOffset);
					indices.add(pointerAddition.apply(inPtrExp));
					values.add(extractBits.apply(returnValue));
				}
			}
		}
		final List<Expression> conjuncts = new ArrayList<>();
		conjuncts.addAll(constructConjunctsForWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray, values,
				indices, useSelectInsteadOfStore));

		final Set<VariableLHS> modifiedGlobals = useSelectInsteadOfStore ? Collections.emptySet()
				: heapDataArrays.stream().map(hda -> hda.getVariableLHS()).collect(Collectors.toSet());

		if (floating2bitvectorTransformationNeeded && !mSettings.useFpToIeeeBvExtension()) {
			final Expression returnValueAsBitvector = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(valueAstType), "#valueAsBitvector",
					new DeclarationInformation(StorageClass.QUANTIFIED, null));

			final Expression transformedToFloat =
					mExpressionTranslation.transformBitvectorToFloat(loc, returnValueAsBitvector, cprimitive);
			final Expression inputValue =
					ExpressionFactory.constructIdentifierExpression(loc, (BoogieType) transformedToFloat.getType(),
							"#value", new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procName));

			final Expression eq =
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, transformedToFloat, inputValue);
			conjuncts.add(eq);
			final Expression conjunction = ExpressionFactory.and(loc, conjuncts);
			final ASTType type = ((TypeHandler) mTypeHandler).byteSize2AstType(loc, cprimitive.getPrimitiveCategory(),
					mTypeSizes.getSize(cprimitive));
			final VarList[] parameters = new VarList[] { new VarList(loc, new String[] { "#valueAsBitvector" }, type) };
			final QuantifierExpression qe =
					new QuantifierExpression(loc, false, new String[0], parameters, new Attribute[0], conjunction);
			swrite.add(mProcedureManager.constructEnsuresSpecification(loc, false, qe, modifiedGlobals));
		} else {
			swrite.add(mProcedureManager.constructEnsuresSpecification(loc, false,
					ExpressionFactory.and(loc, conjuncts), modifiedGlobals));
		}

		mProcedureManager.addSpecificationsToCurrentProcedure(swrite);
		mProcedureManager.endCustomProcedure(main, procName);
	}

	private static List<Expression> constructConjunctsForWriteEnsuresSpecification(final ILocation loc,
			final Collection<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray,
			final List<Expression> values, final List<Expression> indices, final boolean useSelectInsteadOfStore) {
		final List<Expression> conjuncts = new ArrayList<>();
		for (final HeapDataArray other : heapDataArrays) {
			if (heapDataArray == other) {
				conjuncts.add(
						constructHeapArrayUpdateForWriteEnsures(loc, values, indices, other, useSelectInsteadOfStore));
			} else if (useSelectInsteadOfStore) {
				// do nothing (no need to havoc an uninitialized memory cell)
			} else {
				conjuncts.add(constructHeapArrayHardlyModifiedForWriteEnsures(loc, indices, other));
			}

		}
		return conjuncts;
	}

	/**
	 * Note: Currently this returns an empty list, see {@link #constructWriteProcedure} on this topic.
	 *
	 * @param main
	 * @param loc
	 * @param hda
	 * @param rda
	 * @param unchecked
	 *            whether we should construct an unchecked read procedure (i.e. one that omits validity checks)
	 * @return
	 */
	private List<Procedure> constructSingleReadProcedure(final CHandler main, final ILocation loc,
			final HeapDataArray hda, final ReadWriteDefinition rda, final boolean unchecked) {
		// specification for memory reads
		final String returnValue = "#value";
		final ASTType valueAstType = rda.getASTType();
		final String ptrId = "#ptr";
		final String readTypeSize = "#sizeOfReadType";

		final String readProcedureName = unchecked ? rda.getUncheckedReadProcedureName() : rda.getReadProcedureName();

		// create procedure signature
		{
			final ASTType sizetType = mTypeHandler.cType2AstType(loc, mTypeSizeAndOffsetComputer.getSizeT());
			final VarList[] inRead =
					new VarList[] { new VarList(loc, new String[] { ptrId }, mTypeHandler.constructPointerType(loc)),
							new VarList(loc, new String[] { readTypeSize }, sizetType) };

			final VarList[] outRead = new VarList[] { new VarList(loc, new String[] { returnValue }, valueAstType) };
			final Procedure decl = new Procedure(loc, new Attribute[0], readProcedureName, new String[0], inRead,
					outRead, new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, loc, readProcedureName, decl);
		}

		// create procedure specifications
		final ArrayList<Specification> sread = new ArrayList<>();

		if (!unchecked) {
			sread.addAll(constructPointerBaseValidityCheck(loc, ptrId, readProcedureName));

			final Expression sizeRead = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogieTypeForPointerComponents(), readTypeSize,
					new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, readProcedureName));

			sread.addAll(constructPointerTargetFullyAllocatedCheck(loc, sizeRead, ptrId, readProcedureName));
		}

		final Expression arr = hda.getIdentifierExpression();
		final Expression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrId,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, readProcedureName));

		Expression dataFromHeap;
		if (rda.getBytesize() == hda.getSize()) {
			dataFromHeap = constructOneDimensionalArrayAccess(loc, arr, ptrExpr);
		} else if (rda.getBytesize() < hda.getSize()) {
			dataFromHeap = mExpressionTranslation.extractBits(loc,
					constructOneDimensionalArrayAccess(loc, arr, ptrExpr), rda.getBytesize() * 8, 0);
		} else {
			assert rda.getBytesize() % hda.getSize() == 0 : "incompatible sizes";
			final Expression[] dataChunks = new Expression[rda.getBytesize() / hda.getSize()];
			for (int i = 0; i < dataChunks.length; i++) {
				if (i == 0) {
					dataChunks[dataChunks.length - 1 - 0] = constructOneDimensionalArrayAccess(loc, arr, ptrExpr);
				} else {
					final Expression index =
							addIntegerConstantToPointer(loc, ptrExpr, BigInteger.valueOf(i * hda.getSize()));
					dataChunks[dataChunks.length - 1 - i] = constructOneDimensionalArrayAccess(loc, arr, index);
				}
			}
			dataFromHeap = mExpressionTranslation.concatBits(loc, Arrays.asList(dataChunks), hda.getSize());
		}

		if (mMemoryModel instanceof MemoryModel_SingleBitprecise
				&& rda.getCPrimitiveCategory().contains(CPrimitiveCategory.FLOATTYPE)) {
			final CPrimitives cprimitive = rda.getPrimitives().iterator().next();
			dataFromHeap = mExpressionTranslation.transformBitvectorToFloat(loc, dataFromHeap, cprimitive);
		}

		final Expression valueExpr = ExpressionFactory.constructIdentifierExpression(loc,
				mTypeHandler.getBoogieTypeForBoogieASTType(valueAstType), returnValue,
				new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, readProcedureName));
		final Expression equality =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, valueExpr, dataFromHeap);
		sread.add(mProcedureManager.constructEnsuresSpecification(loc, false, equality, Collections.emptySet()));

		mProcedureManager.addSpecificationsToCurrentProcedure(sread);
		mProcedureManager.endCustomProcedure(main, readProcedureName);

		return Collections.emptyList();
	}

	public Expression addIntegerConstantToPointer(final ILocation loc, final Expression ptrExpr,
			final BigInteger integerConstant) {
		final Expression base = getPointerBaseAddress(ptrExpr, loc);
		final Expression offset = getPointerOffset(ptrExpr, loc);
		final Expression addition =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), integerConstant);
		final Expression offsetPlus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, offset,
						mTypeSizeAndOffsetComputer.getSizeT(), addition, mTypeSizeAndOffsetComputer.getSizeT());
		return constructPointerFromBaseAndOffset(base, offsetPlus, loc);
	}

	private static Expression constructOneDimensionalArrayAccess(final ILocation loc, final Expression arr,
			final Expression index) {
		final Expression[] singletonIndex = new Expression[] { index };
		return ExpressionFactory.constructNestedArrayAccessExpression(loc, arr, singletonIndex);
	}

	private static Expression constructOneDimensionalArrayStore(final ILocation loc, final Expression arr,
			final Expression index, final Expression newValue) {
		final Expression[] singletonIndex = new Expression[] { index };
		return ExpressionFactory.constructArrayStoreExpression(loc, arr, singletonIndex, newValue);
	}

	private static Expression constructNestedOneDimensionalArrayStore(final ILocation loc, final Expression arr,
			final List<Expression> indices, final List<Expression> newValues) {
		assert indices.size() == newValues.size();
		Expression result = arr;
		for (int i = 0; i < indices.size(); i++) {
			final Expression[] singletonIndex = new Expression[] { indices.get(i) };
			result = ExpressionFactory.constructArrayStoreExpression(loc, result, singletonIndex, newValues.get(i));
		}
		return result;
	}

	// ensures #memory_X == old(#memory_X)[#ptr := #value];
	private static Expression constructHeapArrayUpdateForWriteEnsures(final ILocation loc,
			final List<Expression> valueExprs, final List<Expression> ptrExprs, final HeapDataArray hda,
			final boolean useSelectInsteadOfStore) {
		final Expression memArray = hda.getIdentifierExpression();
		if (useSelectInsteadOfStore) {
			return ensuresArrayHasValues(loc, valueExprs, ptrExprs, memArray);
		}
		return ensuresArrayNestedUpdate(loc, valueExprs, ptrExprs, memArray);
	}

	// #memory_$Pointer$ == old(#memory_X)[#ptr := #memory_X[#ptr]];
	private static Expression constructHeapArrayHardlyModifiedForWriteEnsures(final ILocation loc,
			final List<Expression> idxExprs, final HeapDataArray hda) {
		final Expression memArray = hda.getIdentifierExpression();
		final List<Expression> newNondetValues = new ArrayList<>();
		for (int i = 0; i < idxExprs.size(); i++) {
			newNondetValues.add(constructOneDimensionalArrayAccess(loc, memArray, idxExprs.get(i)));
		}
		// final Expression memArray = hda.getIdentifierExpression();
		// final Expression aae = constructOneDimensionalArrayAccess(loc, memArray, ptrExpr);
		return ensuresArrayNestedUpdate(loc, newNondetValues, idxExprs, memArray);
	}

	/**
	 * arr == old(arr)[index := newValue]
	 */
	private static Expression ensuresArrayUpdate(final ILocation loc, final Expression newValue, final Expression index,
			final Expression arrayExpr) {
		final Expression oldArray =
				ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
		final Expression ase = constructOneDimensionalArrayStore(loc, oldArray, index, newValue);
		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, arrayExpr, ase);
	}

	private static Expression ensuresArrayNestedUpdate(final ILocation loc, final List<Expression> newValues,
			final List<Expression> indices, final Expression arrayExpr) {
		final Expression oldArray =
				ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
		final Expression ase = constructNestedOneDimensionalArrayStore(loc, oldArray, indices, newValues);
		final Expression eq = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, arrayExpr, ase);
		return eq;
	}

	/**
	 * arr[index] == value
	 */
	private static Expression ensuresArrayHasValue(final ILocation loc, final Expression value, final Expression index,
			final Expression arrayExpr) {
		final Expression select =
				ExpressionFactory.constructNestedArrayAccessExpression(loc, arrayExpr, new Expression[] { index });
		final Expression eq = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, select, value);
		return eq;
	}

	private static Expression ensuresArrayHasValues(final ILocation loc, final List<Expression> values,
			final List<Expression> indices, final Expression arrayExpr) {
		final List<Expression> conjuncts = new ArrayList<>();
		for (int i = 0; i < values.size(); i++) {
			conjuncts.add(ensuresArrayHasValue(loc, values.get(i), indices.get(i), arrayExpr));
		}
		return ExpressionFactory.and(loc, conjuncts);
	}

	/**
	 * Constructs specification that target of pointer is fully allocated. The specification checks that the address of
	 * the pointer plus the size of the type that we read/write is smaller than or equal to the size of the allocated
	 * memory at the base address of the pointer. Furthermore, we check that the offset is greater than or equal to
	 * zero.
	 *
	 * In case mPointerBaseValidity is ASSERTandASSUME, we construct the requires specification
	 * <code>requires (#size + #ptr!offset <= #length[#ptr!base] && 0 <= #ptr!offset)</code>.
	 *
	 * In case mPointerBaseValidity is ASSERTandASSUME, we construct the <b>free</b> requires specification
	 * <code>free requires (#size + #ptr!offset <= #length[#ptr!base] && 0 <= #ptr!offset)</code>.
	 *
	 * In case mPointerBaseValidity is IGNORE, we construct nothing.
	 *
	 * @param loc
	 *            location of translation unit
	 * @param size
	 *            Expression that represents the size of the data type that we read/write at the address of the pointer.
	 * @param ptrName
	 *            name of pointer whose base address is checked
	 * @return A list containing the created specification
	 */
	public List<Specification> constructPointerTargetFullyAllocatedCheck(final ILocation loc, final Expression size,
			final String ptrName, final String procedureName) {
		if (mSettings.getPointerTargetFullyAllocatedMode() == CheckMode.IGNORE) {
			// add nothing
			return Collections.emptyList();
		}
		Expression leq;
		{
			final Expression ptrExpr =
					ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
							new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));

			final Expression ptrBase = getPointerBaseAddress(ptrExpr, loc);
			final Expression aae = ExpressionFactory.constructNestedArrayAccessExpression(loc, getLengthArray(loc),
					new Expression[] { ptrBase });
			final Expression ptrOffset = getPointerOffset(ptrExpr, loc);
			final Expression sum =
					constructPointerBinaryArithmeticExpression(loc, IASTBinaryExpression.op_plus, size, ptrOffset);
			leq = constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, sum, aae);
		}
		final Expression offsetGeqZero;
		{
			final Expression ptrExpr =
					ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
							new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));

			final Expression ptrOffset = getPointerOffset(ptrExpr, loc);
			final Expression nr0 = mTypeSizes.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
			offsetGeqZero =
					constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, nr0, ptrOffset);

		}

		if (mSettings.isBitvectorTranslation()) {
			/*
			 * Check that "#ptr!offset <= #ptr!offset + #sizeOf[Written|Read]Type", i.e., the sum does not overflow.
			 * (This works because #size.. is positive.)
			 */
			final Expression ptrExpr =
					ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
							new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));
			final Expression ptrOffset = getPointerOffset(ptrExpr, loc);
			final Expression sum =
					constructPointerBinaryArithmeticExpression(loc, IASTBinaryExpression.op_plus, size, ptrOffset);
			final Expression noOverFlowInSum =
					constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, ptrOffset, sum);
			leq = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leq, noOverFlowInSum);
		}

		final Expression offsetInAllocatedRange =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leq, offsetGeqZero);
		final boolean isFreeRequires;
		if (mSettings.getPointerTargetFullyAllocatedMode() == CheckMode.ASSERTandASSUME) {
			isFreeRequires = false;
		} else {
			assert mSettings.getPointerTargetFullyAllocatedMode() == CheckMode.ASSUME;
			isFreeRequires = true;
		}
		final RequiresSpecification spec = new RequiresSpecification(loc, isFreeRequires, offsetInAllocatedRange);
		final Check check = new Check(Spec.MEMORY_DEREFERENCE);
		check.annotate(spec);
		return Collections.singletonList(spec);
	}

	/**
	 * Construct specification that the pointer base address is valid. In case
	 * {@link #getPointerBaseValidityCheckMode()} is ASSERTandASSUME, we add the requires specification
	 * <code>requires #valid[#ptr!base]</code>. In case {@link #getPointerBaseValidityCheckMode()} is ASSERTandASSUME,
	 * we add the <b>free</b> requires specification <code>free requires #valid[#ptr!base]</code>. In case
	 * {@link #getPointerBaseValidityCheckMode()} is IGNORE, we add nothing.
	 *
	 * @param loc
	 *            location of translation unit
	 * @param ptrName
	 *            name of pointer whose base address is checked
	 * @param procedureName
	 *            name of the procedure where the specifications will be added
	 * @return A list containing the created specifications.
	 */
	public List<Specification> constructPointerBaseValidityCheck(final ILocation loc, final String ptrName,
			final String procedureName) {
		if (mSettings.getPointerBaseValidityMode() == CheckMode.IGNORE) {
			// add nothing
			return Collections.emptyList();
		}
		final Expression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));
		final Expression isValid = constructPointerBaseValidityCheckExpr(loc, ptrExpr);
		final boolean isFreeRequires;
		if (mSettings.getPointerBaseValidityMode() == CheckMode.ASSERTandASSUME) {
			isFreeRequires = false;
		} else {
			assert mSettings.getPointerBaseValidityMode() == CheckMode.ASSUME;
			isFreeRequires = true;
		}
		final RequiresSpecification spec = new RequiresSpecification(loc, isFreeRequires, isValid);
		final Check check = new Check(Spec.MEMORY_DEREFERENCE);
		check.annotate(spec);
		return Collections.singletonList(spec);
	}

	/**
	 * Compare a pointer component (base or offset) to another expression.
	 *
	 * @param op
	 *            One of the comparison operators defined in {@link IASTBinaryExpression}.
	 */
	private Expression constructPointerBinaryComparisonExpression(final ILocation loc, final int op,
			final Expression left, final Expression right) {
		return mExpressionTranslation.constructBinaryComparisonExpression(loc, op, left,
				mExpressionTranslation.getCTypeOfPointerComponents(), right,
				mExpressionTranslation.getCTypeOfPointerComponents());
	}

	/**
	 * Create an arithmetic expression from a pointer component (base or offset) and another expression.
	 *
	 * @param op
	 *            One of the arithmetic operators defined in {@link IASTBinaryExpression}.
	 */
	private Expression constructPointerBinaryArithmeticExpression(final ILocation loc, final int op,
			final Expression left, final Expression right) {
		return mExpressionTranslation.constructArithmeticExpression(loc, op, left,
				mExpressionTranslation.getCTypeOfPointerComponents(), right,
				mExpressionTranslation.getCTypeOfPointerComponents());
	}

	/**
	 * Generate <code>procedure ULTIMATE.dealloc(~addr:$Pointer$) returns()</code>'s declaration and implementation.
	 * This procedure should be used for deallocations where do not want to check if given memory area is valid (because
	 * we already know this) which is the case, e.g., for arrays that we store on the heap or for alloca.
	 *
	 * @param tuLoc
	 *            the location for the new nodes.
	 *
	 * @return declaration and implementation of procedure <code>Ultimate_dealloc</code>
	 */
	private List<Declaration> declareDeallocation(final CHandler main, final ILocation tuLoc) {
		final Expression bLFalse = mBooleanArrayHelper.constructFalse();
		final Expression addr = ExpressionFactory.constructIdentifierExpression(tuLoc,
				mTypeHandler.getBoogiePointerType(), ADDR, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM,
						MemoryModelDeclarations.ULTIMATE_DEALLOC.getName()));
		final Expression valid = getValidArray(tuLoc);
		final Expression addrBase = ExpressionFactory.constructStructAccessExpression(tuLoc, addr, SFO.POINTER_BASE);
		final Expression[] idcFree = new Expression[] { addrBase };

		{
			final Procedure deallocDeclaration = new Procedure(tuLoc, new Attribute[0],
					MemoryModelDeclarations.ULTIMATE_DEALLOC.getName(), new String[0],
					new VarList[] {
							new VarList(tuLoc, new String[] { ADDR }, mTypeHandler.constructPointerType(tuLoc)) },
					new VarList[0], new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, tuLoc, MemoryModelDeclarations.ULTIMATE_DEALLOC.getName(),
					deallocDeclaration);
		}

		final ArrayList<Specification> specFree = new ArrayList<>();

		final ArrayStoreExpression arrayStore = ExpressionFactory.constructArrayStoreExpression(tuLoc,
				ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, valid), idcFree,
				bLFalse);

		final Expression updateValidArray =
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, valid, arrayStore);

		specFree.add(mProcedureManager.constructEnsuresSpecification(tuLoc, true, updateValidArray,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(valid))));
		mProcedureManager.addSpecificationsToCurrentProcedure(specFree);
		mProcedureManager.endCustomProcedure(main, MemoryModelDeclarations.ULTIMATE_DEALLOC.getName());
		return Collections.emptyList();
	}

	/**
	 * Generate <code>procedure ~Ultimate.alloc(~size:int) returns (#res:$Pointer$);</code>'s declaration and
	 * implementation.
	 *
	 * @param typeHandler
	 * @param tuLoc
	 *            the location for the new nodes.
	 *
	 * @return declaration and implementation of procedure <code>~malloc</code>
	 */
	private ArrayList<Declaration> declareMalloc(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc, final MemoryArea memArea) {
		final MemoryModelDeclarations alloc = memArea.getMemoryModelDeclaration();
		final ASTType intType = typeHandler.cType2AstType(tuLoc, mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression nr0 = mTypeSizes.constructLiteralForIntegerType(tuLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final Expression valid = getValidArray(tuLoc);
		// procedure ~malloc(~size:int) returns (#res:$Pointer$);
		// requires ~size >= 0;
		// ensures old(#valid)[#res!base] = false;
		// ensures #valid = old(#valid)[#res!base := true];
		// ensures #res!offset == 0;
		// ensures #res!base != 0;
		// ensures #length = old(#length)[#res!base := ~size];
		// modifies #length, #valid;
		final Expression res = // new IdentifierExpression(tuLoc, SFO.RES);
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.RES,
						new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, alloc.getName()));

		final Expression length = getLengthArray(tuLoc);
		// #res!base
		final Expression resBase = ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE);
		// { #res!base }
		final Expression[] idcMalloc = new Expression[] { resBase };
		final Expression bLTrue = mBooleanArrayHelper.constructTrue();
		final Expression bLFalse = mBooleanArrayHelper.constructFalse();
		// ~size
		final IdentifierExpression size = // new IdentifierExpression(tuLoc, SIZE);
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(), SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, alloc.getName()));

		{
			final Procedure allocDeclaration = new Procedure(tuLoc, new Attribute[0], alloc.getName(), new String[0],
					new VarList[] { new VarList(tuLoc, new String[] { SIZE }, intType) },
					new VarList[] {
							new VarList(tuLoc, new String[] { SFO.RES }, typeHandler.constructPointerType(tuLoc)) },
					new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, tuLoc, alloc.getName(), allocDeclaration);
		}

		final List<Specification> specMalloc = new ArrayList<>();

		// old(#valid)[#res!base] == false
		specMalloc
				.add(mProcedureManager
						.constructEnsuresSpecification(tuLoc, false,
								ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
										ExpressionFactory.constructNestedArrayAccessExpression(tuLoc,
												ExpressionFactory.constructUnaryExpression(tuLoc,
														UnaryExpression.Operator.OLD, valid),
												idcMalloc),
										bLFalse),
								Collections.emptySet()));
		// #valid == old(#valid)[#res!base := true]
		specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
				ensuresArrayUpdate(tuLoc, bLTrue, resBase, valid),
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(valid))));
		// #res!offset == 0
		specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
						ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_OFFSET), nr0),
				Collections.emptySet()));
		// #res!base != 0
		specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPNEQ,
						ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE), nr0),
				Collections.emptySet()));
		if (memArea == MemoryArea.STACK) {
			// #StackHeapBarrier < res!base
			specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
					mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
							IASTBinaryExpression.op_lessThan, getStackHeapBarrier(tuLoc),
							mExpressionTranslation.getCTypeOfPointerComponents(),
							ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE),
							mExpressionTranslation.getCTypeOfPointerComponents()),
					Collections.emptySet()));
		}
		if (memArea == MemoryArea.HEAP) {
			// res!base < #StackHeapBarrier
			specMalloc.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
					mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
							IASTBinaryExpression.op_lessThan,
							ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE),
							mExpressionTranslation.getCTypeOfPointerComponents(), getStackHeapBarrier(tuLoc),
							mExpressionTranslation.getCTypeOfPointerComponents()),
					Collections.emptySet()));
		}

		// #length == old(#length)[#res!base := ~size]
		specMalloc
				.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
						ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, length,
								ExpressionFactory.constructArrayStoreExpression(tuLoc,
										ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD,
												length),
										idcMalloc, size)),
						Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(length))));
		mProcedureManager.addSpecificationsToCurrentProcedure(specMalloc);

		final ArrayList<Declaration> result = new ArrayList<>();
		if (ADD_IMPLEMENTATIONS) {
			final Expression addr =
					ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), ADDR,
							new DeclarationInformation(StorageClass.LOCAL, alloc.getName()));
			final Expression addrOffset =
					ExpressionFactory.constructStructAccessExpression(tuLoc, addr, SFO.POINTER_OFFSET);
			final Expression addrBase =
					ExpressionFactory.constructStructAccessExpression(tuLoc, addr, SFO.POINTER_BASE);
			// procedure ~malloc(~size:int) returns (#res:pointer) {
			// var ~addr : pointer;
			//
			// assume ~addr!offset = 0;
			// assume ~addr!base != 0;
			// assume !#valid[~addr!base];
			// // #valid setzen
			// #valid = #valid[~addr!base := true];
			// #length = #length[~addr!base := size];
			// // return pointer
			// #res := ~addr;
			// }
			final Expression[] idcAddrBase = new Expression[] { addrBase };
			final VariableDeclaration[] localVars =
					new VariableDeclaration[] { new VariableDeclaration(tuLoc, new Attribute[0], new VarList[] {
							new VarList(tuLoc, new String[] { ADDR }, typeHandler.constructPointerType(tuLoc)) }) };

			final VariableLHS resLhs =
					ExpressionFactory.constructVariableLHS(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.RES,
							new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM, alloc.getName()));
			final Statement[] block = new Statement[6];
			block[0] = new AssumeStatement(tuLoc,
					ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, addrOffset, nr0));
			block[1] = new AssumeStatement(tuLoc,
					ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPNEQ, addrBase, nr0));
			block[2] = new AssumeStatement(tuLoc,
					ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.LOGICNEG,
							ExpressionFactory.constructNestedArrayAccessExpression(tuLoc, valid, idcAddrBase)));
			block[3] =
					StatementFactory.constructAssignmentStatement(tuLoc, new LeftHandSide[] { getValidArrayLhs(tuLoc) },
							new Expression[] { new ArrayStoreExpression(tuLoc, valid, idcAddrBase, bLTrue) });
			block[4] = StatementFactory.constructAssignmentStatement(tuLoc,
					new LeftHandSide[] { getLengthArrayLhs(tuLoc) },
					new Expression[] { new ArrayStoreExpression(tuLoc, length, idcAddrBase, size) });
			block[5] = StatementFactory.constructAssignmentStatement(tuLoc, new LeftHandSide[] { resLhs },
					new Expression[] { addr });

			final Body bodyMalloc = mProcedureManager.constructBody(tuLoc, localVars, block, alloc.getName());
			result.add(new Procedure(tuLoc, new Attribute[0], alloc.getName(), new String[0],
					new VarList[] { new VarList(tuLoc, new String[] { SIZE }, intType) },
					new VarList[] {
							new VarList(tuLoc, new String[] { SFO.RES }, typeHandler.constructPointerType(tuLoc)) },
					null, bodyMalloc));
		}
		mProcedureManager.endCustomProcedure(main, alloc.getName());
		return result;
	}

	/**
	 * Generate declaration of the procedure that we use to allocate memory initially. The signature is the following.
	 * <code>procedure ~Ultimate.allocInit(~size:int, ~ptrBase:int) returns ();</code> See
	 * {@link MemoryModelDeclarations#ULTIMATE_ALLOC_INIT}.
	 */
	private void declareAllocInit(final CHandler main, final ITypeHandler typeHandler, final ILocation tuLoc) {
		final String procedureIdentifier = MemoryModelDeclarations.ULTIMATE_ALLOC_INIT.getName();
		final String pointerBaseIdentifier = "ptrBase";
		final ASTType intType = typeHandler.cType2AstType(tuLoc, mExpressionTranslation.getCTypeOfPointerComponents());
		// #valid
		final Expression valid = getValidArray(tuLoc);
		// #length
		final Expression length = getLengthArray(tuLoc);
		// ~size
		final IdentifierExpression size =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(), SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureIdentifier));
		final IdentifierExpression ptrBase = ExpressionFactory.constructIdentifierExpression(tuLoc,
				mTypeHandler.getBoogieTypeForPointerComponents(), pointerBaseIdentifier,
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureIdentifier));
		{
			final Procedure allocDeclaration =
					new Procedure(tuLoc, new Attribute[0], procedureIdentifier, new String[0],
							new VarList[] { new VarList(tuLoc, new String[] { SIZE, pointerBaseIdentifier }, intType) },
							new VarList[0], new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, tuLoc, procedureIdentifier, allocDeclaration);
		}

		final List<Specification> specs = new ArrayList<>();
		// ensures #valid[ptrBase] == true;
		final Expression bLTrue = mBooleanArrayHelper.constructTrue();
		specs.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
				ensuresArrayHasValue(tuLoc, bLTrue, ptrBase, valid), Collections.emptySet()));
		// ensures #length[ptrBase] == size;
		specs.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
				ensuresArrayHasValue(tuLoc, size, ptrBase, length), Collections.emptySet()));
		if (false) {
			// Omit #StackHeapBarrier here until we know that it is needed.
			// #StackHeapBarrier < res!base
			specs.add(mProcedureManager.constructEnsuresSpecification(tuLoc, false,
					mExpressionTranslation.constructBinaryComparisonIntegerExpression(tuLoc,
							IASTBinaryExpression.op_lessThan, getStackHeapBarrier(tuLoc),
							mExpressionTranslation.getCTypeOfPointerComponents(), ptrBase,
							mExpressionTranslation.getCTypeOfPointerComponents()),
					Collections.emptySet()));
		}
		mProcedureManager.addSpecificationsToCurrentProcedure(specs);
		mProcedureManager.endCustomProcedure(main, procedureIdentifier);
	}

	private static void checkFloatOnHeapSupport(final ILocation loc, final CPrimitive cp) {
		if (SUPPORT_FLOATS_ON_HEAP) {
			return;
		}
		if (cp.isFloatingType()) {
			throw new UnsupportedSyntaxException(loc, FLOAT_ON_HEAP_UNSOUND_MESSAGE);
		}
	}

	private List<Statement> getWriteCallArray(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CArray valueType, final HeapWriteMode writeMode) {

		if (valueType.getValueType().getUnderlyingType() instanceof CArray) {
			throw new UnsupportedSyntaxException(loc,
					"we need to generalize this to nested and/or variable length arrays");
		}

		final BigInteger dimBigInteger = mTypeSizes.extractIntegerValue(valueType.getBound());
		if (dimBigInteger == null) {
			throw new UnsupportedSyntaxException(loc, "variable length arrays not yet supported by this method");
		}

		final Expression arrayStartAddress = hlv.getAddress();
		final Expression newStartAddressBase;
		final Expression newStartAddressOffset;
		if (arrayStartAddress instanceof StructConstructor) {
			newStartAddressBase = ((StructConstructor) arrayStartAddress).getFieldValues()[0];
			newStartAddressOffset = ((StructConstructor) arrayStartAddress).getFieldValues()[1];
		} else {
			newStartAddressBase = MemoryHandler.getPointerBaseAddress(arrayStartAddress, loc);
			newStartAddressOffset = MemoryHandler.getPointerOffset(arrayStartAddress, loc);
		}

		final Expression valueTypeSize = calculateSizeOf(loc, valueType.getValueType());
		final int dim = dimBigInteger.intValue();
		final List<Statement> stmt = new ArrayList<>();

		Expression arrayEntryAddressOffset = newStartAddressOffset;

		for (int pos = 0; pos < dim; pos++) {

			final Expression position = mTypeSizes.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.valueOf(pos));
			final RValue arrayAccessRVal = new RValue(
					ExpressionFactory.constructNestedArrayAccessExpression(loc, value, new Expression[] { position }),
					valueType.getValueType());
			final HeapLValue arrayCellLValue = LRValueFactory.constructHeapLValue(mTypeHandler,
					constructPointerFromBaseAndOffset(newStartAddressBase, arrayEntryAddressOffset, loc),
					valueType.getValueType(), null);
			stmt.addAll(getWriteCall(loc, arrayCellLValue, arrayAccessRVal.getValue(), arrayAccessRVal.getCType(),
					writeMode));
			// TODO 2015-10-11 Matthias: Why is there an addition of value Type size
			// and no multiplication? Check this more carefully.
			arrayEntryAddressOffset =
					mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
							arrayEntryAddressOffset, mExpressionTranslation.getCTypeOfPointerComponents(),
							valueTypeSize, mExpressionTranslation.getCTypeOfPointerComponents());

		}
		return stmt;
	}

	private List<Statement> getWriteCallStruct(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CStructOrUnion valueType, final HeapWriteMode writeMode) {
		final List<Statement> stmt = new ArrayList<>();
		for (final String fieldId : valueType.getFieldIds()) {
			final Expression startAddress = hlv.getAddress();
			final Expression newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			final Expression newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
			final CType fieldType = valueType.getFieldType(fieldId);
			final StructAccessExpression sae = ExpressionFactory.constructStructAccessExpression(loc, value, fieldId);
			final Offset fieldOffset = mTypeSizeAndOffsetComputer.constructOffsetForField(loc, valueType, fieldId);
			if (fieldOffset.isBitfieldOffset()) {
				throw new UnsupportedOperationException("Bitfield write");
			}

			final Expression newOffset = mExpressionTranslation.constructArithmeticExpression(loc,
					IASTBinaryExpression.op_plus, newStartAddressOffset,
					mExpressionTranslation.getCTypeOfPointerComponents(), fieldOffset.getAddressOffsetAsExpression(loc),
					mExpressionTranslation.getCTypeOfPointerComponents());
			final HeapLValue fieldHlv = LRValueFactory.constructHeapLValue(mTypeHandler,
					constructPointerFromBaseAndOffset(newStartAddressBase, newOffset, loc), fieldType, null);
			stmt.addAll(getWriteCall(loc, fieldHlv, sae, fieldType, writeMode));
		}
		return stmt;
	}

	private List<Statement> getWriteCallPointer(final ILocation loc, final HeapLValue hlv, final Expression value,
			final HeapWriteMode writeMode) {
		mRequiredMemoryModelFeatures.reportPointerOnHeapRequired();
		final String writeCallProcedureName = determineWriteProcedureForPointer(writeMode);
		return Collections.singletonList(
				StatementFactory.constructCallStatement(loc, false, new VariableLHS[0], writeCallProcedureName,
						new Expression[] { value, hlv.getAddress(), calculateSizeOf(loc, hlv.getCType()) }));
	}

	private String determineWriteProcedureForPointer(final HeapWriteMode writeMode) throws AssertionError {
		final String writeCallProcedureName;
		switch (writeMode) {
		case SELECT:
			mRequiredMemoryModelFeatures.reportPointerInitWriteRequired();
			writeCallProcedureName = mMemoryModel.getInitPointerProcedureName();
			break;
		case STORE_CHECKED:
			writeCallProcedureName = mMemoryModel.getWritePointerProcedureName();
			break;
		case STORE_UNCHECKED:
			mRequiredMemoryModelFeatures.reportPointerUncheckedWriteRequired();
			writeCallProcedureName = mMemoryModel.getUncheckedWritePointerProcedureName();
			break;
		default:
			throw new AssertionError("todo: add new enum case");
		}
		return writeCallProcedureName;
	}

	private List<Statement> getWriteCallEnum(final ILocation loc, final HeapLValue hlv, final Expression value,
			final HeapWriteMode writeMode) {
		// treat like INT
		return getWriteCallPrimitive(loc, hlv, value, new CPrimitive(CPrimitives.INT), writeMode);
	}

	private List<Statement> getWriteCallPrimitive(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CPrimitive valueType, final HeapWriteMode writeMode) {
		checkFloatOnHeapSupport(loc, valueType);
		mRequiredMemoryModelFeatures.reportDataOnHeapRequired(valueType.getType());

		final String writeCallProcedureName = determineWriteProcedureForPrimitive(valueType, writeMode);

		return Collections.singletonList(
				StatementFactory.constructCallStatement(loc, false, new VariableLHS[0], writeCallProcedureName,
						new Expression[] { value, hlv.getAddress(), calculateSizeOf(loc, hlv.getCType()) }));
	}

	private String determineWriteProcedureForPrimitive(final CPrimitive valueType, final HeapWriteMode writeMode)
			throws AssertionError {
		final String writeCallProcedureName;
		switch (writeMode) {
		case SELECT:
			mRequiredMemoryModelFeatures.reportInitWriteRequired(valueType.getType());
			writeCallProcedureName = mMemoryModel.getInitWriteProcedureName(valueType.getType());
			break;
		case STORE_CHECKED:
			writeCallProcedureName = mMemoryModel.getWriteProcedureName(valueType.getType());
			break;
		case STORE_UNCHECKED:
			mRequiredMemoryModelFeatures.reportUncheckedWriteRequired(valueType.getType());
			writeCallProcedureName = mMemoryModel.getUncheckedWriteProcedureName(valueType.getType());
			break;
		default:
			throw new AssertionError("todo: add new enum case");
		}
		return writeCallProcedureName;
	}

	private MemoryModelDeclarationInfo constructMemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
		switch (mmd) {
		case C_MEMCPY:
			break;
		case C_MEMMOVE:
			break;
		case C_MEMSET:
			break;
		case ULTIMATE_ALLOC_STACK:
			break;
		case ULTIMATE_ALLOC_HEAP:
			break;
		case ULTIMATE_DEALLOC:
			break;
		case ULTIMATE_LENGTH:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() },
							mTypeHandler.getBoogieTypeForSizeT()));
		case ULTIMATE_MEMINIT:
			break;
		case ULTIMATE_PTHREADS_FORK_COUNT:
			return new MemoryModelDeclarationInfo(mmd, mTypeHandler.getBoogieTypeForCType(getThreadIdType()));
		case ULTIMATE_PTHREADS_MUTEX:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() }, mTypeHandler
							.getBoogieTypeForBoogieASTType(getBooleanArrayHelper().constructBoolReplacementType())));
		case ULTIMATE_PTHREADS_RWLOCK:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() },
							mTypeHandler.getBoogieTypeForCType(getRwLockCounterType())));
		case ULTIMATE_VALID:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() },
							mTypeHandler.getBoogieTypeForBoogieASTType(
									getBooleanArrayHelper().constructBoolReplacementType())));
		case ULTIMATE_STACK_HEAP_BARRIER:
			return new MemoryModelDeclarationInfo(mmd, mTypeHandler.getBoogieTypeForPointerComponents());
		case ULTIMATE_DATA_RACE_MEMORY:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() }, mTypeHandler
							.getBoogieTypeForBoogieASTType(getBooleanArrayHelper().constructBoolReplacementType())));
		default:
			break;
		}
		// construct empty mmdi
		return new MemoryModelDeclarationInfo(mmd);
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we lock a mutex that that is already
	 * locked, then the thread blocks.
	 */
	private ArrayList<Declaration> declarePthreadMutexLock(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc) {
		final Expression mutexArray = constructMutexArrayIdentifierExpression(tuLoc);
		final Expression bLTrue = mBooleanArrayHelper.constructTrue();

		declareProcedureWithPointerParam(main, typeHandler, tuLoc,
				MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK.getName(), (inputPtr, res) -> new Specification[] {
						// old(#PthreadsMutex)[#ptr] == false
						mProcedureManager.constructEnsuresSpecification(tuLoc, true,
								constructOldMutexUnlockedCheckExpression(tuLoc, inputPtr), Collections.emptySet()),
						// #PthreadsMutex == old(#PthreadsMutex)[#ptr := true]
						mProcedureManager.constructEnsuresSpecification(tuLoc, true,
								ensuresArrayUpdate(tuLoc, bLTrue, inputPtr, mutexArray),
								Collections
										.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(mutexArray))),
						// we assume that function is always successful and returns 0
						ensuresSuccess(tuLoc, res) });

		return new ArrayList<>();
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we unlock a mutex that has never been
	 * locked, the behavior is undefined. We use a semantics where unlocking a non-locked mutex is a no-op.
	 *
	 * For the return value we follow what GCC did in my experiments. It produced code that returned 0 even if we
	 * unlocked a non-locked mutex.
	 */
	private ArrayList<Declaration> declarePthreadMutexUnlock(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc) {
		final Expression mutexArray = constructMutexArrayIdentifierExpression(tuLoc);
		final Expression bLFalse = mBooleanArrayHelper.constructFalse();

		declareProcedureWithPointerParam(main, typeHandler, tuLoc,
				MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_UNLOCK.getName(), (inputPtr,
						res) -> new Specification[] {
								// #PthreadsMutex == old(#PthreadsMutex)[#ptr := false]
								mProcedureManager.constructEnsuresSpecification(tuLoc, true,
										ensuresArrayUpdate(tuLoc, bLFalse, inputPtr, mutexArray),
										Collections.singleton(
												(VariableLHS) CTranslationUtil.convertExpressionToLHS(mutexArray))),
								// we assume that function is always successful and returns 0
								ensuresSuccess(tuLoc, res) });

		return new ArrayList<>();
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we lock a mutex that that is already
	 * locked, then the function returns an error (non-zero value).
	 */
	private ArrayList<Declaration> declarePthreadMutexTryLock(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc) {
		final Expression zero =
				mTypeSizes.constructLiteralForIntegerType(tuLoc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO);

		final Expression mutexArray = constructMutexArrayIdentifierExpression(tuLoc);
		final Expression bLTrue = mBooleanArrayHelper.constructTrue();

		declareProcedureWithPointerParam(main, typeHandler, tuLoc,
				MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_TRYLOCK.getName(), (inputPtr, res) -> {
					// condition: if mutex unlocked
					final Expression unlocked = constructOldMutexUnlockedCheckExpression(tuLoc, inputPtr);

					// then case: lock the mutex, return 0 (success)
					final Expression lockUpdate = ensuresArrayUpdate(tuLoc, bLTrue, inputPtr, mutexArray);
					final Expression successResult =
							ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, res, zero);

					// else case: mutex unchanged, return non-zero error value
					final Expression lockUnchanged =
							ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, mutexArray, ExpressionFactory
									.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, mutexArray));
					final Expression errorResult = ExpressionFactory.constructUnaryExpression(tuLoc,
							UnaryExpression.Operator.LOGICNEG, successResult);

					return new Specification[] { mProcedureManager.constructEnsuresSpecification(tuLoc, true,
							ExpressionFactory.constructIfThenElseExpression(tuLoc, unlocked,
									ExpressionFactory.and(tuLoc, List.of(lockUpdate, successResult)),
									ExpressionFactory.and(tuLoc, List.of(lockUnchanged, errorResult))),
							Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(mutexArray))) };
				});
		return new ArrayList<>();
	}

	private ArrayList<Declaration> declarePthreadRwLockReadLock(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc) {
		final Expression rwLockArray = constructRwLockArrayIdentifierExpression(tuLoc);

		declareProcedureWithPointerParam(main, typeHandler, tuLoc,
				MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_READLOCK.getName(),
				(inputPtr, res) -> new Specification[] {
						// old(#pthreadsRwLock)[#ptr] >= 0
						mProcedureManager.constructEnsuresSpecification(tuLoc, true,
								constructOldRwLockComparisonExpression(tuLoc, inputPtr,
										IASTBinaryExpression.op_greaterEqual),
								Collections.emptySet()),
						// #pthreadsRwLock == old(#pthreadsRwLock)[#ptr := old(#pthreadsRwLock)[#ptr]+1]
						mProcedureManager.constructEnsuresSpecification(tuLoc, true,
								constructRwLockReadLockUpdate(tuLoc, inputPtr),
								Collections
										.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(rwLockArray))),
						// we assume that function is always successful and returns 0
						ensuresSuccess(tuLoc, res) });
		return new ArrayList<>();
	}

	private ArrayList<Declaration> declarePthreadRwLockWriteLock(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc) {
		final Expression rwLockArray = constructRwLockArrayIdentifierExpression(tuLoc);

		declareProcedureWithPointerParam(main, typeHandler, tuLoc,
				MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_WRITELOCK.getName(), (inputPtr,
						res) -> new Specification[] {
								// old(#pthreadsRwLock)[#ptr] == 0
								mProcedureManager.constructEnsuresSpecification(tuLoc, true,
										constructOldRwLockComparisonExpression(tuLoc, inputPtr,
												IASTBinaryExpression.op_equals),
										Collections.emptySet()),
								// #pthreadsRwLock == old(#pthreadsRwLock)[#ptr := -1]
								mProcedureManager.constructEnsuresSpecification(tuLoc, true,
										constructRwLockWriteLockUpdate(tuLoc, inputPtr),
										Collections.singleton(
												(VariableLHS) CTranslationUtil.convertExpressionToLHS(rwLockArray))),
								// we assume that function is always successful and returns 0
								ensuresSuccess(tuLoc, res) });
		return new ArrayList<>();
	}

	private ArrayList<Declaration> declarePthreadRwLockUnlock(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc) {
		final Expression rwLockArray = constructRwLockArrayIdentifierExpression(tuLoc);
		final Expression zero =
				mTypeSizes.constructLiteralForIntegerType(tuLoc, getRwLockCounterType(), BigInteger.ZERO);

		declareProcedureWithPointerParam(main, typeHandler, tuLoc,
				MemoryModelDeclarations.ULTIMATE_PTHREADS_RWLOCK_UNLOCK.getName(), (inputPtr, res) -> {
					final Expression oldLockCounter =
							ExpressionFactory
									.constructNestedArrayAccessExpression(tuLoc,
											ExpressionFactory.constructUnaryExpression(tuLoc,
													UnaryExpression.Operator.OLD, rwLockArray),
											new Expression[] { inputPtr });
					final Expression newLockCounter =
							mExpressionTranslation
									.constructArithmeticExpression(tuLoc, IASTBinaryExpression.op_minus, oldLockCounter,
											getRwLockCounterType(), mTypeSizes.constructLiteralForIntegerType(tuLoc,
													getRwLockCounterType(), BigInteger.valueOf(1L)),
											getRwLockCounterType());
					return new Specification[] {
							// #pthreadsRwLock == old(#pthreadsRwLock)[#ptr := if old(#pthreadsRwLock)[#ptr] > 0 then
							// old(#pthreadsRwLock)[#ptr] - 1 else 0]
							mProcedureManager.constructEnsuresSpecification(tuLoc, true,
									ensuresArrayUpdate(tuLoc,
											ExpressionFactory.constructIfThenElseExpression(tuLoc,
													constructOldRwLockComparisonExpression(tuLoc, inputPtr,
															IASTBinaryExpression.op_greaterThan),
													newLockCounter, zero),
											inputPtr, rwLockArray),
									Collections.emptySet()),
							// we assume that function is always successful and returns 0
							ensuresSuccess(tuLoc, res) };
				});
		return new ArrayList<>();
	}

	// #pthreadsRwLock == old(#pthreadsRwLock)[#ptr := old(#pthreadsRwLock)[#ptr]+1]
	private Expression constructRwLockReadLockUpdate(final ILocation tuLoc, final Expression inputPtr) {
		final Expression rwLockArray = constructRwLockArrayIdentifierExpression(tuLoc);
		final Expression oldLockCounter = ExpressionFactory.constructNestedArrayAccessExpression(tuLoc,
				ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, rwLockArray),
				new Expression[] { inputPtr });
		final Expression newLockCounter = mExpressionTranslation.constructArithmeticExpression(tuLoc,
				IASTBinaryExpression.op_plus, oldLockCounter, getRwLockCounterType(),
				mTypeSizes.constructLiteralForIntegerType(tuLoc, getRwLockCounterType(), BigInteger.valueOf(1L)),
				getRwLockCounterType());
		return ensuresArrayUpdate(tuLoc, newLockCounter, inputPtr, rwLockArray);
	}

	// #pthreadsRwLock == old(#pthreadsRwLock)[#ptr := -1]
	private Expression constructRwLockWriteLockUpdate(final ILocation tuLoc, final Expression inputPtr) {
		final Expression rwLockArray = constructRwLockArrayIdentifierExpression(tuLoc);
		final Expression newLockCounter =
				mTypeSizes.constructLiteralForIntegerType(tuLoc, getRwLockCounterType(), BigInteger.valueOf(-1L));
		return ensuresArrayUpdate(tuLoc, newLockCounter, inputPtr, rwLockArray);
	}

	// ensures (#res == 0)
	private EnsuresSpecification ensuresSuccess(final ILocation loc, final Expression res) {
		final Expression zero =
				mTypeSizes.constructLiteralForIntegerType(loc, new CPrimitive(CPrimitives.INT), BigInteger.ZERO);
		return mProcedureManager.constructEnsuresSpecification(loc, true,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, res, zero), Collections.emptySet());
	}

	// old(#PthreadsMutex)[#inputPtr] == false
	private Expression constructOldMutexUnlockedCheckExpression(final ILocation loc, final Expression inputPtr) {
		final Expression mutexArray = constructMutexArrayIdentifierExpression(loc);
		final Expression bLFalse = mBooleanArrayHelper.constructFalse();

		return ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
				ExpressionFactory.constructNestedArrayAccessExpression(loc,
						ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, mutexArray),
						new Expression[] { inputPtr }),
				bLFalse);
	}

	// old(#pthreadsRwLock)[#inputPtr] >= 0
	private Expression constructOldRwLockComparisonExpression(final ILocation loc, final Expression inputPtr,
			final int op) {
		final Expression rwLockArray = constructRwLockArrayIdentifierExpression(loc);
		final Expression lockCounter = ExpressionFactory.constructNestedArrayAccessExpression(loc,
				ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, rwLockArray),
				new Expression[] { inputPtr });
		final Expression zero = mExpressionTranslation.constructZero(loc, getRwLockCounterType());
		return mExpressionTranslation.constructBinaryComparisonExpression(loc, op, lockCounter, getRwLockCounterType(),
				zero, getRwLockCounterType());
	}

	private void declareProcedureWithPointerParam(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc, final String name,
			final BiFunction<Expression, Expression, Specification[]> getSpecs) {
		final String inputPointerIdentifier = "#inputPtr";
		final ASTType inputPointerAstType =
				typeHandler.cType2AstType(tuLoc, new CPointer(new CPrimitive(CPrimitives.VOID)));
		final String resultIdentifier = SFO.RES;
		final CType resultCType = new CPrimitive(CPrimitives.INT);
		final ASTType resultAstType = typeHandler.cType2AstType(tuLoc, resultCType);
		final BoogieType resultBoogieType = typeHandler.getBoogieTypeForCType(resultCType);

		final Expression inputPointerExpression =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(),
						inputPointerIdentifier, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, name));
		final Expression resultIdentifierExpression = ExpressionFactory.constructIdentifierExpression(tuLoc,
				resultBoogieType, resultIdentifier, new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, name));

		final Procedure procDecl = new Procedure(tuLoc, new Attribute[0], name, new String[0],
				new VarList[] { new VarList(tuLoc, new String[] { inputPointerIdentifier }, inputPointerAstType) },
				new VarList[] { new VarList(tuLoc, new String[] { resultIdentifier }, resultAstType) },
				new Specification[0], null);
		mProcedureManager.beginCustomProcedure(main, tuLoc, name, procDecl);
		mProcedureManager.addSpecificationsToCurrentProcedure(
				Arrays.asList(getSpecs.apply(inputPointerExpression, resultIdentifierExpression)));
		mProcedureManager.endCustomProcedure(main, name);
	}

	/**
	 * Sets the heap at the given base address to all 0s. Analyzes the given type to check which heap arrays should be
	 * updated.
	 *
	 * Note that the type does not need to be an array type. A struct containing large arrays should also trigger this
	 * kind of initialization.
	 *
	 * @param loc
	 * @param baseAddress
	 * @param cType
	 * @return
	 */
	public List<Statement> getInitializationForOnHeapVariableOfAggregateOrUnionType(final ILocation loc,
			final HeapLValue baseAddress, final CType cType) {
		assert CTranslationUtil.isAggregateOrUnionType(cType) : "Argument is not aggregate or union but " + cType;

		final Set<CType> relevantBaseTypes = CTranslationUtil.extractNonAggregateNonUnionTypes(cType);

		return getInitializationForHeapAtPointer(loc, baseAddress, relevantBaseTypes);
	}

	private List<Statement> getInitializationForHeapAtPointer(final ILocation loc, final HeapLValue baseAddress,
			final Set<CType> relevantBaseTypes) throws AssertionError {
		// first collect the concerned heap arrays (in a set, to avoid duplicates)
		final Set<HeapDataArray> relevantHeapArrays = new LinkedHashSet<>();
		for (final CType baseType : relevantBaseTypes) {
			assert !(baseType instanceof CNamed);
			if (baseType instanceof CPointer) {
				mRequiredMemoryModelFeatures.reportPointerOnHeapRequired();
				final HeapDataArray hda = mMemoryModel.getPointerHeapArray();
				mRequiredMemoryModelFeatures.reportPointerOnHeapInitFunctionRequired();
				relevantHeapArrays.add(hda);
			} else if (baseType instanceof CPrimitive) {
				final CPrimitives primitive = ((CPrimitive) baseType).getType();
				mRequiredMemoryModelFeatures.reportDataOnHeapRequired(primitive);
				final HeapDataArray hda = mMemoryModel.getDataHeapArray(primitive);
				mRequiredMemoryModelFeatures.reportDataOnHeapInitFunctionRequired(primitive);
				relevantHeapArrays.add(hda);
			} else if (baseType instanceof CEnum) {
				final CPrimitives primitive = CPrimitives.INT;
				mRequiredMemoryModelFeatures.reportDataOnHeapRequired(primitive);
				final HeapDataArray hda = mMemoryModel.getDataHeapArray(primitive);
				mRequiredMemoryModelFeatures.reportDataOnHeapInitFunctionRequired(primitive);
				relevantHeapArrays.add(hda);
			} else {
				throw new AssertionError("unforseen case");
			}
		}

		final List<Statement> result = new ArrayList<>();
		// second construct the respective initialization call for each relevant heap array
		for (final HeapDataArray relevantHeapArray : relevantHeapArrays) {
			result.add(getInitializationForHeapArrayAtAddress(loc, relevantHeapArray, baseAddress));
		}
		return result;
	}

	private static Statement getInitializationForHeapArrayAtAddress(final ILocation loc,
			final HeapDataArray relevantHeapArray, final HeapLValue baseAddress) {
		return StatementFactory.constructAssignmentStatement(loc,
				new VariableLHS[] { relevantHeapArray.getVariableLHS() },
				new Expression[] { ExpressionFactory.constructFunctionApplication(loc,
						getNameOfHeapInitFunction(relevantHeapArray),
						new Expression[] { relevantHeapArray.getIdentifierExpression(),
								getPointerBaseAddress(baseAddress.getAddress(), loc) },
						(BoogieType) relevantHeapArray.getIdentifierExpression().getType()) });
	}

	private static String getNameOfHeapInitFunction(final HeapDataArray relevantHeapArray) {
		return SFO.AUXILIARY_FUNCTION_PREFIX + SFO.INIT_TO_ZERO_AT_ADDRESS + relevantHeapArray.getName();
	}

	public String getNameOfHeapStoreFunction(final HeapDataArray relevantHeapArray) {
		return SFO.AUXILIARY_FUNCTION_PREFIX + SFO.STORE_SUBARRAY_AT_ADDRESS + relevantHeapArray.getName();
	}

	public String getNameOfHeapSelectFunction(final HeapDataArray relevantHeapArray) {
		return SFO.AUXILIARY_FUNCTION_PREFIX + SFO.SELECT_SUBARRAY_AT_ADDRESS + relevantHeapArray.getName();
	}

	/**
	 * (workaround that is necessary because or memory arrays are multidimensional instead of nested)
	 *
	 * @param heapDataArray
	 */
	private void declareDataOnHeapStoreFunction(final HeapDataArray heapDataArray) {
		final CACSLLocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final CPrimitive cTypeOfPointerComponents = mExpressionTranslation.getCTypeOfPointerComponents();
		final ASTType astTypeOfPointerComponents = mTypeHandler.cType2AstType(ignoreLoc, cTypeOfPointerComponents);

		// compute zeros of matching type
		final BoogieType heapContentBoogieType = heapDataArray.getArrayContentBoogieType();
		final BoogieType flattenedType =
				StructExpanderUtil.flattenType(heapContentBoogieType, new HashMap<>(), new HashMap<>());

		final String[] subarraysToStore;
		if (flattenedType instanceof BoogieStructType) {
			final BoogieStructType bst = (BoogieStructType) flattenedType;
			subarraysToStore = new String[bst.getFieldCount()];

			for (int fieldNr = 0; fieldNr < bst.getFieldCount(); fieldNr++) {
				final String param = FunctionDeclarations.constructNameForFunctionInParam(2);
				subarraysToStore[fieldNr] = param + StructExpanderUtil.DOT + bst.getFieldIds()[fieldNr];
			}
		} else {
			final String param = FunctionDeclarations.constructNameForFunctionInParam(2);
			subarraysToStore = new String[] { param };
		}

		final Attribute[] attributes =
				constructExpandAndSmtDefinedAttributesForSubArrayStore(heapDataArray, subarraysToStore);

		final BoogieType hdaBoogieType = (BoogieType) heapDataArray.getIdentifierExpression().getType();

		final BoogieType innerArrayBoogieType = BoogieType.createArrayType(0,
				new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() }, heapContentBoogieType);

		// register the FunctionDeclaration so it will be added at the end of translation
		mExpressionTranslation.getFunctionDeclarations().declareFunction(ignoreLoc,
				getNameOfHeapStoreFunction(heapDataArray), attributes, hdaBoogieType.toASTType(ignoreLoc),
				hdaBoogieType.toASTType(ignoreLoc), astTypeOfPointerComponents,
				innerArrayBoogieType.toASTType(ignoreLoc));
	}

	/**
	 * Selects a subarray of the two dimensional heap array
	 *
	 * @param heapDataArray
	 */
	private void declareDataOnHeapSelectFunction(final HeapDataArray heapDataArray) {
		final CACSLLocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final CPrimitive cTypeOfPointerComponents = mExpressionTranslation.getCTypeOfPointerComponents();
		final ASTType astTypeOfPointerComponents = mTypeHandler.cType2AstType(ignoreLoc, cTypeOfPointerComponents);

		final BoogieType heapContentBoogieType = heapDataArray.getArrayContentBoogieType();
		final BoogieType hdaBoogieType = (BoogieType) heapDataArray.getIdentifierExpression().getType();

		final BoogieType flattenedType =
				StructExpanderUtil.flattenType(heapContentBoogieType, new HashMap<>(), new HashMap<>());
		final BoogieType innerArrayBoogieType = BoogieType.createArrayType(0,
				new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() }, heapContentBoogieType);

		final String[] subarraysToStore;
		if (flattenedType instanceof BoogieStructType) {
			final BoogieStructType bst = (BoogieStructType) flattenedType;
			subarraysToStore = new String[bst.getFieldCount()];

			for (int fieldNr = 0; fieldNr < bst.getFieldCount(); fieldNr++) {
				final String param = FunctionDeclarations.constructNameForFunctionInParam(1);
				subarraysToStore[fieldNr] = param;
			}
		} else {
			final String param = FunctionDeclarations.constructNameForFunctionInParam(1);
			subarraysToStore = new String[] { param };
		}

		final Attribute[] attributes =
				constructExpandAndSmtDefinedAttributesForSubArraySelect(heapDataArray, subarraysToStore);

		mExpressionTranslation.getFunctionDeclarations().declareFunction(ignoreLoc,
				getNameOfHeapSelectFunction(heapDataArray), attributes, innerArrayBoogieType.toASTType(ignoreLoc),
				hdaBoogieType.toASTType(ignoreLoc), astTypeOfPointerComponents);

	}

	private void declareDataOnHeapInitFunction(final HeapDataArray heapDataArray) {
		final CACSLLocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final CPrimitive cTypeOfPointerComponents = mExpressionTranslation.getCTypeOfPointerComponents();
		final ASTType astTypeOfPointerComponents = mTypeHandler.cType2AstType(ignoreLoc, cTypeOfPointerComponents);
		final BoogieType boogieTypeOfPointerComponents1 =
				mTypeHandler.getBoogieTypeForBoogieASTType(astTypeOfPointerComponents);
		final String smtSortOfPointerComponents1 =
				CTranslationUtil.getSmtSortStringForBoogieType(boogieTypeOfPointerComponents1);

		// compute zeros of matching type
		final BoogieType heapContentBoogieType = heapDataArray.getArrayContentBoogieType();
		final BoogieType flattenedType =
				StructExpanderUtil.flattenType(heapContentBoogieType, new HashMap<>(), new HashMap<>());

		final String[] subarraysToStore;
		if (flattenedType instanceof BoogieStructType) {
			final BoogieStructType bst = (BoogieStructType) flattenedType;
			subarraysToStore = new String[bst.getFieldCount()];

			for (int fieldNr = 0; fieldNr < bst.getFieldCount(); fieldNr++) {
				final String zero = CTranslationUtil.getSmtZeroStringForBoogieType(bst.getFieldType(fieldNr));
				final String contentType = CTranslationUtil.getSmtSortStringForBoogieType(bst.getFieldType(fieldNr));
				subarraysToStore[fieldNr] =
						String.format("((as const (Array %s %s)) %s)", smtSortOfPointerComponents1, contentType, zero);
			}
		} else {
			final String zero = CTranslationUtil.getSmtZeroStringForBoogieType(heapContentBoogieType);

			final String contentType = CTranslationUtil.getSmtSortStringForBoogieType(heapContentBoogieType);

			final String subarrayToStore =
					String.format("((as const (Array %s %s)) %s)", smtSortOfPointerComponents1, contentType, zero);

			subarraysToStore = new String[] { subarrayToStore };
		}

		final Attribute[] attributes =
				constructExpandAndSmtDefinedAttributesForSubArrayStore(heapDataArray, subarraysToStore);

		// register the FunctionDeclaration so it will be added at the end of translation
		mExpressionTranslation.getFunctionDeclarations().declareFunction(ignoreLoc,
				getNameOfHeapInitFunction(heapDataArray), attributes,
				((BoogieType) heapDataArray.getIdentifierExpression().getType()).toASTType(ignoreLoc),
				((BoogieType) heapDataArray.getIdentifierExpression().getType()).toASTType(ignoreLoc),
				astTypeOfPointerComponents);

	}

	private Attribute[] constructExpandAndSmtDefinedAttributesForSubArrayStore(final HeapDataArray heapDataArray,
			final String... subArrayToStore) {
		final Attribute[] attributes;
		final List<Attribute> attributeList = new ArrayList<>();

		final CACSLLocation ignoreLoc1 = LocationFactory.createIgnoreCLocation();
		final CPrimitive cTypeOfPointerComponents1 = mExpressionTranslation.getCTypeOfPointerComponents();

		mTypeHandler.cType2AstType(ignoreLoc1, cTypeOfPointerComponents1);

		final BoogieType heapContentBoogieType = heapDataArray.getArrayContentBoogieType();
		// should not be necessary, doing just to be safe in case we add heap arrays with more complicated types
		final BoogieType flattenedType =
				StructExpanderUtil.flattenType(heapContentBoogieType, new HashMap<>(), new HashMap<>());

		if (flattenedType instanceof BoogieStructType) {
			final BoogieStructType bst = (BoogieStructType) flattenedType;

			for (int fieldNr = 0; fieldNr < bst.getFieldCount(); fieldNr++) {

				// add expand attribute
				final NamedAttribute expandAttribute =
						new NamedAttribute(ignoreLoc1, StructExpanderUtil.ATTRIBUTE_EXPAND_STRUCT, new Expression[] {
								ExpressionFactory.createStringLiteral(ignoreLoc1, bst.getFieldIds()[fieldNr]) });
				attributeList.add(expandAttribute);

				final String smtDefinition = String.format("(store %s %s %s)",
						FunctionDeclarations.constructNameForFunctionInParam(0) + StructExpanderUtil.DOT
								+ bst.getFieldIds()[fieldNr],
						FunctionDeclarations.constructNameForFunctionInParam(1), subArrayToStore[fieldNr]);

				final NamedAttribute namedAttribute =
						new NamedAttribute(ignoreLoc1, FunctionDeclarations.SMTDEFINED_IDENTIFIER,
								new Expression[] { ExpressionFactory.createStringLiteral(ignoreLoc1, smtDefinition) });
				attributeList.add(namedAttribute);
			}
		} else {
			final String smtDefinition =
					String.format("(store %s %s %s)", FunctionDeclarations.constructNameForFunctionInParam(0),
							FunctionDeclarations.constructNameForFunctionInParam(1), subArrayToStore[0]);

			final NamedAttribute namedAttribute =
					new NamedAttribute(ignoreLoc1, FunctionDeclarations.SMTDEFINED_IDENTIFIER,
							new Expression[] { ExpressionFactory.createStringLiteral(ignoreLoc1, smtDefinition) });
			attributeList.add(namedAttribute);
		}

		attributes = attributeList.toArray(new Attribute[attributeList.size()]);
		return attributes;
	}

	private Attribute[] constructExpandAndSmtDefinedAttributesForSubArraySelect(final HeapDataArray heapDataArray,
			final String... indices) {
		final Attribute[] attributes;
		final List<Attribute> attributeList = new ArrayList<>();

		final CACSLLocation ignoreLoc1 = LocationFactory.createIgnoreCLocation();
		final CPrimitive cTypeOfPointerComponents1 = mExpressionTranslation.getCTypeOfPointerComponents();

		mTypeHandler.cType2AstType(ignoreLoc1, cTypeOfPointerComponents1);

		final BoogieType heapContentBoogieType = heapDataArray.getArrayContentBoogieType();
		// should not be necessary, doing just to be safe in case we add heap arrays with more complicated types
		final BoogieType flattenedType =
				StructExpanderUtil.flattenType(heapContentBoogieType, new HashMap<>(), new HashMap<>());

		if (flattenedType instanceof BoogieStructType) {
			final BoogieStructType bst = (BoogieStructType) flattenedType;

			for (int fieldNr = 0; fieldNr < bst.getFieldCount(); fieldNr++) {

				// add expand attribute
				final NamedAttribute expandAttribute =
						new NamedAttribute(ignoreLoc1, StructExpanderUtil.ATTRIBUTE_EXPAND_STRUCT, new Expression[] {
								ExpressionFactory.createStringLiteral(ignoreLoc1, bst.getFieldIds()[fieldNr]) });
				attributeList.add(expandAttribute);

				final String smtDefinition = String.format("(select %s %s)",
						FunctionDeclarations.constructNameForFunctionInParam(0) + StructExpanderUtil.DOT
								+ bst.getFieldIds()[fieldNr],
						FunctionDeclarations.constructNameForFunctionInParam(1), indices[fieldNr]);

				final NamedAttribute namedAttribute =
						new NamedAttribute(ignoreLoc1, FunctionDeclarations.SMTDEFINED_IDENTIFIER,
								new Expression[] { ExpressionFactory.createStringLiteral(ignoreLoc1, smtDefinition) });
				attributeList.add(namedAttribute);
			}
		} else {

			final String smtDefinition =
					String.format("(select %s %s)", FunctionDeclarations.constructNameForFunctionInParam(0),
							FunctionDeclarations.constructNameForFunctionInParam(1), indices[0]);

			final NamedAttribute namedAttribute =
					new NamedAttribute(ignoreLoc1, FunctionDeclarations.SMTDEFINED_IDENTIFIER,
							new Expression[] { ExpressionFactory.createStringLiteral(ignoreLoc1, smtDefinition) });
			attributeList.add(namedAttribute);
		}

		attributes = attributeList.toArray(new Attribute[attributeList.size()]);
		return attributes;
	}

	/**
	 * Construct assert statements that do memsafety checks for {@link pointerValue} if the corresponding settings are
	 * active. settings concerned are: - "Pointer base address is valid at dereference" - "Pointer to allocated memory
	 * at dereference"
	 *
	 * @param loc
	 *            TODO
	 * @param pointerValue
	 *            TODO
	 * @param standardFunctionHandler
	 *            TODO
	 * @param expressionTranslation
	 *            TODO
	 */
	public List<Statement> constructMemsafetyChecksForPointerExpression(final ILocation loc,
			final Expression pointerValue) {
		final List<Statement> result = new ArrayList<>();
		if (mSettings.getPointerBaseValidityMode() != CheckMode.IGNORE) {

			// valid[s.base]
			final Expression validBase = constructPointerBaseValidityCheckExpr(loc, pointerValue);

			if (mSettings.getPointerBaseValidityMode() == CheckMode.ASSERTandASSUME) {
				final AssertStatement assertion = new AssertStatement(loc, validBase);
				final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
				chk.annotate(assertion);
				result.add(assertion);
			} else {
				assert mSettings.getPointerBaseValidityMode() == CheckMode.ASSUME : "missed a case?";
				final Statement assume = new AssumeStatement(loc, validBase);
				result.add(assume);
			}
		}
		if (mSettings.getPointerTargetFullyAllocatedMode() != CheckMode.IGNORE) {

			// s.offset < length[s.base])
			final Expression offsetSmallerLength = mExpressionTranslation.constructBinaryComparisonIntegerExpression(
					loc, IASTBinaryExpression.op_lessThan, MemoryHandler.getPointerOffset(pointerValue, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(),
					ExpressionFactory.constructNestedArrayAccessExpression(loc, getLengthArray(loc),
							new Expression[] { MemoryHandler.getPointerBaseAddress(pointerValue, loc) }),
					mExpressionTranslation.getCTypeOfPointerComponents());

			// s.offset >= 0;
			final Expression offsetNonnegative = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_greaterEqual, MemoryHandler.getPointerOffset(pointerValue, loc),
					mExpressionTranslation.getCTypeOfPointerComponents(), mTypeSizes.constructLiteralForIntegerType(loc,
							mExpressionTranslation.getCTypeOfPointerComponents(), new BigInteger("0")),
					mExpressionTranslation.getCTypeOfPointerComponents());

			final Expression aAndB =
					// new BinaryExpression(loc, Operator.LOGICAND, offsetSmallerLength, offsetNonnegative);
					ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, offsetSmallerLength,
							offsetNonnegative);
			if (mSettings.getPointerBaseValidityMode() == CheckMode.ASSERTandASSUME) {
				final AssertStatement assertion = new AssertStatement(loc, aAndB);
				final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
				chk.annotate(assertion);
				result.add(assertion);
			} else {
				assert mSettings.getPointerBaseValidityMode() == CheckMode.ASSUME : "missed a case?";
				final Statement assume = new AssumeStatement(loc, aAndB);
				result.add(assume);
			}
		}
		return result;
	}

	public interface IBooleanArrayHelper {
		ASTType constructBoolReplacementType();

		Expression constructTrue();

		Expression constructFalse();

		Expression compareWithTrue(Expression expr);

		default Expression constructValue(final boolean value) {
			return value ? constructTrue() : constructFalse();
		}
	}

	public static final class BooleanArrayHelper_Bool implements IBooleanArrayHelper {

		@Override
		public ASTType constructBoolReplacementType() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new PrimitiveType(ignoreLoc, BoogieType.TYPE_BOOL, "bool");
		}

		@Override
		public Expression constructTrue() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.createBooleanLiteral(ignoreLoc, true);
		}

		@Override
		public Expression constructFalse() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.createBooleanLiteral(ignoreLoc, false);
		}

		@Override
		public Expression compareWithTrue(final Expression expr) {
			return expr;
		}

	}

	public static final class BooleanArrayHelper_Integer implements IBooleanArrayHelper {

		@Override
		public ASTType constructBoolReplacementType() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new PrimitiveType(ignoreLoc, BoogieType.TYPE_INT, "int");
		}

		@Override
		public Expression constructTrue() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.createIntegerLiteral(ignoreLoc, "1");
		}

		@Override
		public Expression constructFalse() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.createIntegerLiteral(ignoreLoc, "0");
		}

		@Override
		public Expression compareWithTrue(final Expression expr) {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ, expr, constructTrue());
		}

	}

	public static final class BooleanArrayHelper_Bitvector implements IBooleanArrayHelper {

		@Override
		public ASTType constructBoolReplacementType() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return new PrimitiveType(ignoreLoc, BoogieType.createBitvectorType(1), "bv1");
		}

		@Override
		public Expression constructTrue() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.createBitvecLiteral(ignoreLoc, "1", 1);
		}

		@Override
		public Expression constructFalse() {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.createBitvecLiteral(ignoreLoc, "0", 1);
		}

		@Override
		public Expression compareWithTrue(final Expression expr) {
			final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
			return ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ, expr, constructTrue());
		}
	}

	class MemoryModelDeclarationInfo {

		private final MemoryModelDeclarations mMmd;
		private final BoogieType mBoogieType;

		public MemoryModelDeclarationInfo(final MemoryModelDeclarations mmd) {
			mMmd = mmd;
			mBoogieType = null;
		}

		public MemoryModelDeclarationInfo(final MemoryModelDeclarations mmd, final BoogieType boogieType) {
			mMmd = mmd;
			mBoogieType = boogieType;
		}

		IdentifierExpression constructIdentifierExpression(final ILocation loc) {
			return ExpressionFactory.constructIdentifierExpression(loc, mBoogieType, mMmd.getName(),
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
		}

		VariableLHS constructVariableLHS(final ILocation loc) {
			return ExpressionFactory.constructVariableLHS(loc, mBoogieType, mMmd.getName(),
					DeclarationInformation.DECLARATIONINFO_GLOBAL);
		}

		BoogieType getBoogieType() {
			if (mBoogieType == null) {
				throw new IllegalStateException();
			}
			return mBoogieType;
		}

	}

}
