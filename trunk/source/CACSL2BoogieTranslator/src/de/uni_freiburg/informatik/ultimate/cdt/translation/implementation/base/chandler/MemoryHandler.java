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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
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
import de.uni_freiburg.informatik.ultimate.boogie.ast.ModifiesSpecification;
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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TypeHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.BaseMemoryModel.ReadWriteDefinition;
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
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check.Spec;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.MemoryModel;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerCheckMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.LinkedScopedHashMap;

/**
 * @author Markus Lindenmann
 */
public class MemoryHandler {

	public static enum MemoryModelDeclarations {
		Ultimate_Alloc(SFO.ALLOC),

		Ultimate_Dealloc(SFO.DEALLOC),

		/**
		 * (used for calloc)
		 */
		Ultimate_MemInit(SFO.MEMINIT),

		C_Memcpy(SFO.C_MEMCPY),

		C_Memmove(SFO.C_MEMMOVE),

		C_Memset(SFO.C_MEMSET),

		C_StrCpy(SFO.C_STRCPY),

		Ultimate_Length(SFO.LENGTH),

		Ultimate_Pthreads_Mutex("#PthreadsMutex"),

		ULTIMATE_PTHREADS_MUTEX_LOCK("#PthreadsMutexLock"),

		Ultimate_Valid(SFO.VALID);

		private final String mName;

		MemoryModelDeclarations(final String name) {
			mName = name;
		}

		public String getName() {
			return mName;
		}

		/**
		 *
		 * @param rmmf
		 * @param settings
		 * @return true iff the method execution made a change in rmmf
		 */
		boolean resolveDependencies(final RequiredMemoryModelFeatures rmmf, final TranslationSettings settings) {
			if (this == MemoryModelDeclarations.C_Memcpy || this == MemoryModelDeclarations.C_Memmove) {
				return memcpyOrMemmoveRequirements(rmmf);
			} else if (this == MemoryModelDeclarations.C_Memset) {
				return false;
			} else if (this == MemoryModelDeclarations.Ultimate_MemInit) {
				return meminitRequirements(rmmf, settings);
			} else if (this == MemoryModelDeclarations.C_StrCpy) {
				return strcpyRequirements(rmmf, settings);
			} else {
				return false;
			}
		}

		private boolean strcpyRequirements(final RequiredMemoryModelFeatures rmmf, final TranslationSettings settings) {
			boolean changedSomething = false;
			for (final CPrimitives prim : rmmf.mDataOnHeapRequired) {
				changedSomething |= rmmf.reportUncheckedWriteRequired(prim);
			}
			if (rmmf.mPointerOnHeapRequired) {
				changedSomething |= rmmf.reportPointerUncheckedWriteRequired();
			}
			return changedSomething;
		}

		private boolean meminitRequirements(final RequiredMemoryModelFeatures rmmf,
				final TranslationSettings settings) {
			boolean changedSomething = false;
			if (settings.useConstantArrays()) {
				for (final CPrimitives prim : rmmf.mDataOnHeapRequired) {
					changedSomething |= rmmf.reportDataOnHeapInitFunctionRequired(prim);
				}
				if (rmmf.isPointerOnHeapRequired()) {
					changedSomething |= rmmf.reportPointerOnHeapInitFunctionRequired();
				}
			}
			/*
			 * at the moment meminit is using manual assignments, not write calls, that should perhaps be changed
			 *  --> and then we need to add the corresponding code here, like e.g. for memmove
			 */
			return changedSomething;
		}

		boolean memcpyOrMemmoveRequirements(final RequiredMemoryModelFeatures mmf) {
			boolean changedSomething = false;
			for (final CPrimitives prim : mmf.mDataOnHeapRequired) {
				changedSomething |= mmf.reportUncheckedWriteRequired(prim);
			}
			if (mmf.mPointerOnHeapRequired) {
				changedSomething |= mmf.reportPointerUncheckedWriteRequired();
			}
			return changedSomething;
		}

	}


	private static enum HeapWriteMode {
		Store_Checked,
		Store_Unchecked,
		Select
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

		mRequiredMemoryModelFeatures = new RequiredMemoryModelFeatures();//prerunMemoryHandler.mRequiredMemoryModelFeatures;
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

	public Expression calculateSizeOf(final ILocation loc, final CType cType, final IASTNode hook) {
		return mTypeSizeAndOffsetComputer.constructBytesizeExpression(loc, cType, hook);
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
			final IASTNode hook) {
		if (!mRequiredMemoryModelFeatures.isMemoryModelInfrastructureRequired()
				&& mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations().isEmpty()) {
			return Collections.emptyList();
		}

		mRequiredMemoryModelFeatures.finish(mSettings);

		final ArrayList<Declaration> decl = new ArrayList<>();

		decl.add(constructNullPointerConstant());
		decl.add(constructValidArrayDeclaration());
		decl.add(constuctLengthArrayDeclaration());

		final Collection<HeapDataArray> heapDataArrays = mMemoryModel.getDataHeapArrays(mRequiredMemoryModelFeatures);

		{
			// add memory arrays and read/write procedures
			for (final HeapDataArray heapDataArray : heapDataArrays) {
				decl.add(constructMemoryArrayDeclaration(tuLoc, heapDataArray.getName(), heapDataArray.getASTType()));
				// create and add read and write procedure
				decl.addAll(constructWriteProcedures(main, tuLoc, heapDataArrays, heapDataArray, hook));
				decl.addAll(constructReadProcedures(main, tuLoc, heapDataArray, hook));

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

		decl.addAll(declareDeallocation(main, tuLoc, hook));

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.Ultimate_Alloc)) {
			decl.addAll(declareMalloc(main, mTypeHandler, tuLoc, hook));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_Memset)) {
			decl.addAll(declareMemset(main, heapDataArrays, hook));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.Ultimate_MemInit)) {
			decl.addAll(declareUltimateMeminit(main, heapDataArrays, hook));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_Memcpy)) {
			decl.addAll(declareMemcpyOrMemmove(main, heapDataArrays, MemoryModelDeclarations.C_Memcpy, hook));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_Memmove)) {
			decl.addAll(declareMemcpyOrMemmove(main, heapDataArrays, MemoryModelDeclarations.C_Memmove, hook));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.C_StrCpy)) {
			decl.addAll(declareStrCpy(main, heapDataArrays, hook));
		}


		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.Ultimate_Pthreads_Mutex)) {
			decl.add(declarePThreadsMutexArray(tuLoc));
		}

		if (mRequiredMemoryModelFeatures.getRequiredMemoryModelDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK)) {
			decl.addAll(declarePthreadMutexLock(main, mTypeHandler, tuLoc, hook));
		}
		assert assertContainsNodeProcedureDeclarations(decl) : "add procedure declarations via function handler!";
		return decl;
	}

	public CallStatement constructUltimateMeminitCall(final ILocation loc, final Expression amountOfFields,
			final Expression sizeOfFields, final Expression product, final Expression pointer) {
		requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_MemInit);
		return StatementFactory.constructCallStatement(loc, false, new VariableLHS[0],
				MemoryModelDeclarations.Ultimate_MemInit.getName(),
				new Expression[] { pointer, amountOfFields, sizeOfFields, product });
	}

	/**
	 * Returns call to our memset procedure and announces that memset is required by our memory model.
	 */
	public CallStatement constructUltimateMemsetCall(final ILocation loc, final Expression pointer,
			final Expression value, final Expression amount, final VariableLHS resVar) {
		requireMemoryModelFeature(MemoryModelDeclarations.C_Memset);
		return StatementFactory.constructCallStatement(loc, false, new VariableLHS[] { resVar },
				MemoryModelDeclarations.C_Memset.getName(), new Expression[] { pointer, value, amount });
	}

	public CallStatement constructPthreadMutexLockCall(final ILocation loc, final Expression pointer,
			final VariableLHS variableLHS) {
		requireMemoryModelFeature(MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK);
		return StatementFactory.constructCallStatement(loc, false, new VariableLHS[] { variableLHS },
				MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK.getName(), new Expression[] { pointer });
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
		requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Length);
		final MemoryModelDeclarationInfo validMmfInfo =
				getMemoryModelDeclarationInfo(MemoryModelDeclarations.Ultimate_Length);
		return validMmfInfo.constructIdentiferExpression(loc);
	}

	/**
	 * @param loc
	 *            location of translation unit
	 * @return new IdentifierExpression that represents the <em>#length array</em>
	 */
	public VariableLHS getLengthArrayLhs(final ILocation loc) {
		requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Length);
		final MemoryModelDeclarationInfo validMmfInfo =
				getMemoryModelDeclarationInfo(MemoryModelDeclarations.Ultimate_Length);
		return validMmfInfo.constructVariableLHS(loc);

	}

	/**
	 * @param loc
	 *            location of translation unit
	 * @return new IdentifierExpression that represents the <em>#valid array</em>
	 */
	public Expression getValidArray(final ILocation loc) {
		requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Valid);
		final MemoryModelDeclarationInfo validMmfInfo =
				getMemoryModelDeclarationInfo(MemoryModelDeclarations.Ultimate_Valid);
		return validMmfInfo.constructIdentiferExpression(loc);
	}

	public VariableLHS getValidArrayLhs(final ILocation loc) {
		requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Valid);
		final MemoryModelDeclarationInfo validMmfInfo =
				getMemoryModelDeclarationInfo(MemoryModelDeclarations.Ultimate_Valid);
		return validMmfInfo.constructVariableLHS(loc);
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
			final AssertStatement offsetZero = new AssertStatement(loc,
					ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, addrOffset, nr0));
			check.annotate(offsetZero);
			result.add(offsetZero);

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
		requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Dealloc);
		// Further checks are done in the precondition of ~free()!
		return StatementFactory.constructCallStatement(loc, false, new VariableLHS[0],
				MemoryModelDeclarations.Ultimate_Dealloc.getName(), new Expression[] { lrVal.getValue() });
	}

	/**
	 *
	 * @param callerName
	 *            name of the calling procedure
	 */
	public CallStatement getMallocCall(final LocalLValue resultPointer, final ILocation loc, final IASTNode hook) {
		return getMallocCall(calculateSizeOf(loc, resultPointer.getCType(), hook), (VariableLHS) resultPointer.getLhs(),
				loc);
	}

	/**
	 *
	 * @param surroundingProcedure
	 *            name of the procedure that the generated statements will be added to.
	 */
	public CallStatement getMallocCall(final Expression size, final VariableLHS returnedValue, final ILocation loc) {
		requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Alloc);
		final CallStatement result =
				StatementFactory.constructCallStatement(loc, false, new VariableLHS[] { returnedValue },
						MemoryModelDeclarations.Ultimate_Alloc.getName(), new Expression[] { size });

		mProcedureManager.registerProcedure(MemoryModelDeclarations.Ultimate_Alloc.getName());
		return result;
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
	public ExpressionResult getReadCall(final Expression address, final CType resultType, final IASTNode hook) {
		final ILocation loc = address.getLocation();
		final boolean bitvectorConversionNeeded = false;

		ExpressionResultBuilder resultBuilder = new ExpressionResultBuilder();

		final String readCallProcedureName;
		{

			final CType ut = resultType.getUnderlyingType();

			if (ut instanceof CPrimitive) {
				final CPrimitive cp = (CPrimitive) ut;
				checkFloatOnHeapSupport(loc, cp);
				mRequiredMemoryModelFeatures.reportDataOnHeapRequired(cp.getType());
				readCallProcedureName = mMemoryModel.getReadProcedureName(cp.getType());
			} else if (ut instanceof CPointer) {
				mRequiredMemoryModelFeatures.reportPointerOnHeapRequired();
				readCallProcedureName = mMemoryModel.getReadPointerProcedureName();
			} else if (ut instanceof CNamed) {
				throw new AssertionError("we took underlying type");
			} else if (ut instanceof CArray) {
				// we assume it is an Array on Heap
				// assert main.cHandler.isHeapVar(((IdentifierExpression) lrVal.getValue()).getIdentifier());
				// but it may not only be on heap, because it is addressoffed, but also because it is inside
				// a struct that is addressoffed..
				mRequiredMemoryModelFeatures.reportPointerOnHeapRequired();
				readCallProcedureName = mMemoryModel.getReadPointerProcedureName();
			} else if (ut instanceof CEnum) {
				// enum is treated like an int
				mRequiredMemoryModelFeatures.reportDataOnHeapRequired(CPrimitives.INT);
				readCallProcedureName = mMemoryModel.getReadProcedureName(CPrimitives.INT);
			} else {
				throw new UnsupportedOperationException("unsupported type " + ut);
			}
		}

		// TODO: bitvectorConversionNeeded switches between two identical branches --> what was the real intention??
		final ASTType returnedValueAstType;
		if (bitvectorConversionNeeded) {
			returnedValueAstType = mTypeHandler.cType2AstType(loc, resultType);
		} else {
			returnedValueAstType = mTypeHandler.cType2AstType(loc, resultType);
		}
		final AuxVarInfo auxvar = mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MEMREAD);
		resultBuilder.addDeclaration(auxvar.getVarDec());
		resultBuilder.addAuxVar(auxvar);

		final VariableLHS[] lhss = new VariableLHS[] { auxvar.getLhs() };
		final CallStatement call = StatementFactory.constructCallStatement(loc, false, lhss, readCallProcedureName, // heapType.toString(),
				new Expression[] { address, calculateSizeOf(loc, resultType, hook) });
		for (final Overapprox overapprItem : resultBuilder.getOverappr()) {
			overapprItem.annotate(call);
		}
		resultBuilder.addStatement(call);
		assert CTranslationUtil.isAuxVarMapComplete(mNameHandler, resultBuilder);

		// ExpressionResult result;
		if (bitvectorConversionNeeded) {
			final IdentifierExpression returnedValueIdExpr = auxvar.getExp();

			resultBuilder.setLrValue(new RValue(returnedValueIdExpr, resultType));

			final ExpressionResult intermediateResult = mExpressionTranslation.convertIntToInt(loc,
					resultBuilder.build(), (CPrimitive) resultType.getUnderlyingType());
			resultBuilder = new ExpressionResultBuilder().addAllExceptLrValue(intermediateResult)
					.setLrValue(intermediateResult.getLrValue());

			final AuxVarInfo bvReturnedValueAux =
					mAuxVarInfoBuilder.constructAuxVarInfo(loc, resultType, SFO.AUXVAR.MEMREAD);
			resultBuilder.addDeclaration(bvReturnedValueAux.getVarDec());
			resultBuilder.addAuxVar(bvReturnedValueAux);

			final VariableLHS[] bvlhss = new VariableLHS[] { bvReturnedValueAux.getLhs() };
			final AssignmentStatement as =
					// mProcedureManager.constructAssignmentStatement(loc, bvlhss, new Expression[] {
					// result.getLrValue().getValue() });
					StatementFactory.constructAssignmentStatement(loc, bvlhss,
							new Expression[] { resultBuilder.getLrValue().getValue() });
			// stmt.add(as);
			resultBuilder.addStatement(as);
			// TODO is it correct to use returnedValueAstType here?
			// result.setLrValue(new RValue(bvReturnedValueAux.getExp(), resultType));
			resultBuilder.resetLrValue(new RValue(bvReturnedValueAux.getExp(), resultType));
		} else {
			final IdentifierExpression returnedValueIdExpr = ExpressionFactory.constructIdentifierExpression(loc,
					mTypeHandler.getBoogieTypeForBoogieASTType(returnedValueAstType), auxvar.getExp().getIdentifier(),
					new DeclarationInformation(StorageClass.LOCAL, mProcedureManager.getCurrentProcedureID()));
			resultBuilder.setLrValue(new RValue(returnedValueIdExpr, resultType));
		}
		// return result;
		return resultBuilder.build();
	}

	/**
	 * Generates a procedure call to writeT(val, ptr), writing val to the according memory array. (for the C-methode the
	 * argument order is value, target, for this method it's the other way around)
	 *
	 * @param hlv
	 *            the HeapLvalue containing the address to write to
	 * @param rval
	 *            the value to write.
	 * @param isStaticInitialization
	 *            If the write call is used during static initialization of global variables, we can use the unchecked
	 *            methods and omit various specifications.
	 *
	 * @return the required Statements to perform the write.
	 */
	public List<Statement> getWriteCall(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CType valueType, final boolean isStaticInitialization, final IASTNode hook) {
		final CType realValueType = valueType.getUnderlyingType();

		final HeapWriteMode writeMode =
				isStaticInitialization ? HeapWriteMode.Store_Unchecked : HeapWriteMode.Store_Checked;
		return getWriteCall(loc, hlv, value, realValueType, writeMode, hook);
	}

	private List<Statement> getWriteCall(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CType valueType, final HeapWriteMode writeMode, final IASTNode hook) {
		final CType realValueType = valueType.getUnderlyingType();

		if (realValueType instanceof CPrimitive) {
			return getWriteCallPrimitive(loc, hlv, value, (CPrimitive) realValueType, writeMode, hook);
		} else if (realValueType instanceof CEnum) {
			return getWriteCallEnum(loc, hlv, value, writeMode, hook);
		} else if (realValueType instanceof CPointer) {
			return getWriteCallPointer(loc, hlv, value, writeMode, hook);
		} else if (realValueType instanceof CStructOrUnion) {
			return getWriteCallStruct(loc, hlv, value, (CStructOrUnion) realValueType, writeMode, hook);
		} else if (realValueType instanceof CArray) {
			return getWriteCallArray(loc, hlv, value, (CArray) realValueType, writeMode, hook);
		} else {
			throw new UnsupportedSyntaxException(loc, "we don't recognize this type: " + realValueType);
		}
	}

	/**
	 * Like {@link #getWriteCall(ILocation, HeapLValue, Expression, CType, boolean, IASTNode)}, but working under the
	 * assumption that the to-be-written heap cells are uninitialized so far. Thus we can use "select-constraints"
	 * instead of "store-constraints" for the heap array.
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
		return getWriteCall(loc, hlv, value, realValueType, HeapWriteMode.Select, hook);
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
		return ExpressionFactory.constructStructAccessExpression(loc, pointer, "base");
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
		return ExpressionFactory.constructStructAccessExpression(loc, pointer, "offset");
	}

	public static StructConstructor constructPointerFromBaseAndOffset(final Expression base, final Expression offset,
			final ILocation loc) {
		return ExpressionFactory.constructStructConstructor(loc, new String[] { "base", "offset" },
				new Expression[] { base, offset });
	}

	/**
	 * Takes a loop or function body and inserts mallocs and frees for all the identifiers in this.mallocedAuxPointers
	 *
	 * Note that this returns a statement block that is like the given block but with added statement in front
	 * <b>and</b>in the back!
	 */
	public List<Statement> insertMallocs(final List<Statement> block, final IASTNode hook) {
		final List<Statement> mallocs = new ArrayList<>();
		for (final LocalLValueILocationPair llvp : mVariablesToBeMalloced.currentScopeKeys()) {
			mallocs.add(this.getMallocCall(llvp.llv, llvp.loc, hook));
		}
		final List<Statement> frees = new ArrayList<>();
		for (final LocalLValueILocationPair llvp : mVariablesToBeFreed.currentScopeKeys()) { // frees are inserted in
			// handleReturnStm
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
	 *
	 * @return a pointer of the form: {base: ptr.base, offset: ptr.offset + integer * sizeof(valueType)}
	 */
	public Expression doPointerArithmetic(final int operator, final ILocation loc, final Expression ptrAddress,
			final RValue integer, final CType valueType, final IASTNode hook) {
		if (mTypeSizes.getSize(((CPrimitive) integer.getCType().getUnderlyingType()).getType()) != mTypeSizes
				.getSize(mExpressionTranslation.getCTypeOfPointerComponents().getType())) {
			throw new UnsupportedOperationException("not yet implemented, conversion is needed");
		}
		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(ptrAddress, loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(ptrAddress, loc);
		final Expression timesSizeOf = multiplyWithSizeOfAnotherType(loc, valueType, integer.getValue(),
				mExpressionTranslation.getCTypeOfPointerComponents(), hook);
		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, operator, pointerOffset,
				mExpressionTranslation.getCTypeOfPointerComponents(), timesSizeOf,
				mExpressionTranslation.getCTypeOfPointerComponents());
		final StructConstructor newPointer = MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
		return newPointer;
	}

	/**
	 * Like {@link #doPointerArithmetic(int, ILocation, Expression, RValue, CType, IASTNode)} but additionally the
	 * integer operand is converted to the same type that we use to represent pointer components. As a consequence we
	 * have to return an ExpressionResult.
	 */
	public ExpressionResult doPointerArithmeticWithConversion(final int operator, final ILocation loc,
			final Expression ptrAddress, final RValue integer, final CType valueType, final IASTNode hook) {
		final ExpressionResult eres = mExpressionTranslation.convertIntToInt(loc, new ExpressionResult(integer),
				mExpressionTranslation.getCTypeOfPointerComponents());
		final Expression resultExpression =
				doPointerArithmetic(operator, loc, ptrAddress, (RValue) eres.getLrValue(), valueType, hook);
		final RValue newRValue = new RValue(resultExpression, mExpressionTranslation.getCTypeOfPointerComponents());
		return new ExpressionResultBuilder().addAllExceptLrValue(eres).setLrValue(newRValue).build();
	}

	/**
	 * Multiply an integerExpresion with the size of another type.
	 *
	 * @param integerExpresionType
	 *            {@link CType} whose translation is the Boogie type of integerExpression and the result.
	 * @return An {@link Expression} that represents <i>integerExpression * sizeof(valueType)</i>
	 */
	public Expression multiplyWithSizeOfAnotherType(final ILocation loc, final CType valueType,
			final Expression integerExpression, final CPrimitive integerExpresionType, final IASTNode hook) {
		final Expression timesSizeOf;
		timesSizeOf = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_multiply,
				integerExpression, integerExpresionType, calculateSizeOf(loc, valueType, hook), integerExpresionType);
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

	public Expression constructMutexArrayIdentifierExpression(final ILocation loc) {
		requireMemoryModelFeature(MemoryModelDeclarations.Ultimate_Pthreads_Mutex);
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
				final BigInteger fst =
						mTypeSizes.extractIntegerValue(fieldValues[0], new CPrimitive(CPrimitives.LONG), null);
				final BigInteger snd =
						mTypeSizes.extractIntegerValue(fieldValues[1], new CPrimitive(CPrimitives.LONG), null);
				if (BigInteger.ZERO.equals(fst) && BigInteger.ZERO.equals(snd)) {
					return true;
				}
			}
		}
		final BigInteger integerValue = mTypeSizes.extractIntegerValue(expr, new CPrimitive(CPrimitives.LONG), null);
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
				memoryModel = new MemoryModel_SingleBitprecise(1, mTypeSizes, (TypeHandler) mTypeHandler,
						mExpressionTranslation);
				break;
			case HoenickeLindenmann_2ByteResolution:
				memoryModel = new MemoryModel_SingleBitprecise(2, mTypeSizes, (TypeHandler) mTypeHandler,
						mExpressionTranslation);
				break;
			case HoenickeLindenmann_4ByteResolution:
				memoryModel = new MemoryModel_SingleBitprecise(4, mTypeSizes, (TypeHandler) mTypeHandler,
						mExpressionTranslation);
				break;
			case HoenickeLindenmann_8ByteResolution:
				memoryModel = new MemoryModel_SingleBitprecise(8, mTypeSizes, (TypeHandler) mTypeHandler,
						mExpressionTranslation);
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
				new VarList(ignoreLoc, new String[] { MemoryModelDeclarations.Ultimate_Valid.getName() }, validType);
		return new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] { vlV });
	}

	private VariableDeclaration constructNullPointerConstant() {
		// NULL Pointer
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final VariableDeclaration result = new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] {
				new VarList(ignoreLoc, new String[] { SFO.NULL }, mTypeHandler.constructPointerType(ignoreLoc)) });
		return result;
	}

	private List<Declaration> declareUltimateMeminit(final CHandler main,
			final Collection<HeapDataArray> heapDataArrays, final IASTNode hook) {
		final ArrayList<Declaration> decls = new ArrayList<>();
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final String inParamPtr = "#ptr";
		final String inParamAmountOfFields = "#amountOfFields";
		final String inParamSizeOfFields = "#sizeOfFields";
		final String inParamProduct = "#product";
		final String procName = MemoryModelDeclarations.Ultimate_MemInit.getName();

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

			final IdentifierExpression pointerIdExpr = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
					mTypeHandler.getBoogiePointerType(),
					inParamPtr, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));
			final HeapLValue hlv = LRValueFactory.constructHeapLValue(mTypeHandler, pointerIdExpr,
							new CPointer(new CPrimitive(CPrimitives.VOID)), null);

			final Set<CType> cPrimitivesWithRequiredHeapArray =
					mRequiredMemoryModelFeatures.getDataOnHeapRequired().stream()
						.map(cPrim -> new CPrimitive(cPrim)).collect(Collectors.toSet());
			stmt.addAll(getInitializationForHeapAtPointer(ignoreLoc, hlv, cPrimitivesWithRequiredHeapArray));

		} else {
			final CPrimitive sizeT = mTypeSizeAndOffsetComputer.getSizeT();
			final AuxVarInfo loopCtrAux = mAuxVarInfoBuilder.constructAuxVarInfo(ignoreLoc, sizeT, SFO.AUXVAR.LOOPCTR);
			decl.add(loopCtrAux.getVarDec());

			final Expression zero = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
					new CPrimitive(CPrimitives.UCHAR), BigInteger.ZERO);
			final List<Statement> loopBody =
					constructMemsetLoopBody(heapDataArrays, loopCtrAux, inParamPtr, zero, procName, hook);

			final IdentifierExpression inParamProductExpr =
					ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
							inParamProduct, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));

			final Expression stepsize;
			if (mMemoryModel instanceof MemoryModel_SingleBitprecise) {
				final int resolution = ((MemoryModel_SingleBitprecise) mMemoryModel).getResolution();
				stepsize = mTypeSizes.constructLiteralForIntegerType(ignoreLoc, sizeT, BigInteger.valueOf(resolution));
			} else {
				final IdentifierExpression inParamSizeOfFieldsExpr =
						ExpressionFactory.constructIdentifierExpression(ignoreLoc, BoogieType.TYPE_INT,
								inParamSizeOfFields,
								new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));

				stepsize = inParamSizeOfFieldsExpr;
			}

			stmt.addAll(constructCountingLoop(constructBoundExitCondition(inParamProductExpr, loopCtrAux), loopCtrAux,
					stepsize, loopBody, procName));
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
	 * Construct specification and implementation for our Boogie representation of the memcpy and memmove functions
	 * defined in 7.24.2.1 of C11.
	 *
	 * void *memcpy(void * restrict s1, const void * restrict s2, size_t n);
	 *
	 * void *memmove( void* dest, const void* src, size_t count );
	 *
	 * @param main
	 * @param heapDataArrays
	 * @return
	 */
	private List<Declaration> declareMemcpyOrMemmove(final CHandler main,
			final Collection<HeapDataArray> heapDataArrays, final MemoryModelDeclarations memCopyOrMemMove,
			final IASTNode hook) {
		assert memCopyOrMemMove == MemoryModelDeclarations.C_Memcpy
				|| memCopyOrMemMove == MemoryModelDeclarations.C_Memmove;

		final List<Declaration> memCpyDecl = new ArrayList<>();
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final VarList inPDest =
				new VarList(ignoreLoc, new String[] { SFO.MEMCPY_DEST }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList inPSrc =
				new VarList(ignoreLoc, new String[] { SFO.MEMCPY_SRC }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList inPSize = new VarList(ignoreLoc, new String[] { SFO.MEMCPY_SIZE },
				mTypeHandler.cType2AstType(ignoreLoc, mTypeSizeAndOffsetComputer.getSizeT()));
		final VarList outP =
				new VarList(ignoreLoc, new String[] { SFO.RES }, mTypeHandler.constructPointerType(ignoreLoc));
		final VarList[] inParams = new VarList[] { inPDest, inPSrc, inPSize };
		final VarList[] outParams = new VarList[] { outP };

		{
			final Procedure memCpyProcDecl = new Procedure(ignoreLoc, new Attribute[0], memCopyOrMemMove.getName(),
					new String[0], inParams, outParams, new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, ignoreLoc, memCopyOrMemMove.getName(), memCpyProcDecl);
		}

		final List<Declaration> decl = new ArrayList<>();
		final CPrimitive sizeT = mTypeSizeAndOffsetComputer.getSizeT();

		final AuxVarInfo loopCtrAux = mAuxVarInfoBuilder.constructAuxVarInfo(ignoreLoc, sizeT, SFO.AUXVAR.LOOPCTR);
		decl.add(loopCtrAux.getVarDec());

		final ExpressionResult loopBody =
				constructMemcpyOrMemmoveLoopAssignment(heapDataArrays, loopCtrAux, SFO.MEMCPY_DEST,
						SFO.MEMCPY_SRC, memCopyOrMemMove.getName(), hook);
		decl.addAll(loopBody.getDeclarations());

		final IdentifierExpression sizeIdExprBody = // new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SIZE);
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
						SFO.MEMCPY_SIZE,
						new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, memCopyOrMemMove.getName()));




		final Expression one = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
		final List<Statement> stmt =
				constructCountingLoop(constructBoundExitCondition(sizeIdExprBody, loopCtrAux),
						loopCtrAux, one, loopBody.getStatements(),
						memCopyOrMemMove.getName());

		final Body procBody =
				mProcedureManager.constructBody(ignoreLoc, decl.toArray(new VariableDeclaration[decl.size()]),
						stmt.toArray(new Statement[stmt.size()]), memCopyOrMemMove.getName());

		// make the specifications
		final ArrayList<Specification> specs = new ArrayList<>();

		// add modifies spec

		// EDIT: the function handler should completely deal with modifies clauses if we announce them correctly

		final IdentifierExpression sizeIdExprDecl = // new IdentifierExpression(ignoreLoc, SFO.MEMCPY_SIZE);
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
						SFO.MEMCPY_SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, memCopyOrMemMove.getName()));

		// add requires #valid[dest!base];
		specs.addAll(constructPointerBaseValidityCheck(ignoreLoc, SFO.MEMCPY_DEST, memCopyOrMemMove.getName()));
		// add requires #valid[src!base];
		specs.addAll(constructPointerBaseValidityCheck(ignoreLoc, SFO.MEMCPY_SRC, memCopyOrMemMove.getName()));

		// add requires (#size + #dest!offset <= #length[#dest!base] && 0 <= #dest!offset)
		specs.addAll(constructPointerTargetFullyAllocatedCheck(ignoreLoc, sizeIdExprDecl, SFO.MEMCPY_DEST,
				memCopyOrMemMove.getName()));

		// add requires (#size + #src!offset <= #length[#src!base] && 0 <= #src!offset)
		specs.addAll(constructPointerTargetFullyAllocatedCheck(ignoreLoc, sizeIdExprDecl, SFO.MEMCPY_SRC,
				memCopyOrMemMove.getName()));

		// free ensures #res == dest;
		final EnsuresSpecification returnValue =
				mProcedureManager.constructEnsuresSpecification(
						ignoreLoc, true, ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ,
								ExpressionFactory.constructIdentifierExpression(ignoreLoc,
										mTypeHandler.getBoogiePointerType(), SFO.RES,
										new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM,
												memCopyOrMemMove.getName())),
								ExpressionFactory
										.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(),
												SFO.MEMCPY_DEST, new DeclarationInformation(
														StorageClass.PROC_FUNC_INPARAM, memCopyOrMemMove.getName()))),
						Collections.emptySet());
		specs.add(returnValue);

		// add the procedure declaration
		mProcedureManager.addSpecificationsToCurrentProcedure(specs);

		// add the procedure implementation
		final Procedure memCpyProc = new Procedure(ignoreLoc, new Attribute[0], memCopyOrMemMove.getName(),
				new String[0], inParams, outParams, null, procBody);
		memCpyDecl.add(memCpyProc);

		mProcedureManager.endCustomProcedure(main, memCopyOrMemMove.getName());

		return memCpyDecl;
	}


	/**
	 * Construct a loop condition of the form
	 * loopCounterAux < loopBoundVariableExpr
	 *
	 * @param loopBoundVariableExpr
	 * @param loopCounterAux
	 * @return
	 */
	private Expression constructBoundExitCondition(final Expression loopBoundVariableExpr, final AuxVarInfo loopCounterAux) {
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
	private List<Declaration> declareStrCpy(final CHandler main, final Collection<HeapDataArray> heapDataArrays,
			final IASTNode hook) {

		final MemoryModelDeclarations strcpyMmDecl = MemoryModelDeclarations.C_StrCpy;
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

		final CPrimitive charCType = new CPrimitive(CPrimitives.CHAR);

		final Expression srcId =
					ExpressionFactory.constructIdentifierExpression(ignoreLoc,
							mTypeHandler.getBoogiePointerType(),
							SFO.STRCPY_SRC,
							new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, strcpyMmDecl.getName()));
		final Expression destId =
					ExpressionFactory.constructIdentifierExpression(ignoreLoc,
							mTypeHandler.getBoogiePointerType(),
							SFO.STRCPY_DEST,
							new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, strcpyMmDecl.getName()));


		// construct the body of the loop (except for the offset incrementing, that is done by constructCountingLoop
		final List<Statement> loopBody = new ArrayList<>();
		{
			final Expression currentSrc = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, srcId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					charCType, hook);
			final Expression currentDest = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, destId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					charCType, hook);

			/* do pointer validity checks for current pointers (src/dest + offset) (using #valid and #length)
			 *
			 * assert #valid[src!base] == 1;
			 * assert src!offset + #t~offset15 * 1 < #length[src!base] && src!offset + #t~offset15 * 1 >= 0;
			 * assert #valid[dest!base] == 1;
			 * assert dest!offset + #t~offset15 * 1 < #length[dest!base] && dest!offset + #t~offset15 * 1 >= 0;
			 */
			{
				final List<Statement> checkSrcPtr =
						constructMemsafetyChecksForPointerExpression(ignoreLoc, currentSrc);
				loopBody.addAll(checkSrcPtr);

				final List<Statement> checkDestPtr =
						constructMemsafetyChecksForPointerExpression(ignoreLoc, currentDest);
				loopBody.addAll(checkDestPtr);
			}

			/* check that dest and src do not overlap (that would be undefined behaviour)
			 *
			 * assert src!base != src!base ||
			 *           (dest!offset + #t~offset15 * 1 < src!offset && src!offset + #t~offset15 * 1 < dest!offset);
			 *
			 * TODO: if and when we want to check for this kind of undefined behavior, we should activate this check
			 */
			final boolean checkForStringCopyOverlapingUndefindeBehaviour = false;
			if (checkForStringCopyOverlapingUndefindeBehaviour){
				final Expression basesDistinct = ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPNEQ,
						getPointerBaseAddress(currentSrc, ignoreLoc),
						getPointerBaseAddress(currentSrc, ignoreLoc));
				final Expression destDoesNotReachIntoSrc = ExpressionFactory.newBinaryExpression(ignoreLoc,
						Operator.COMPLT,
						getPointerOffset(currentDest, ignoreLoc),
						getPointerOffset(srcId, ignoreLoc));
				final Expression srcDoesNotReachIntoDest = ExpressionFactory.newBinaryExpression(ignoreLoc,
						Operator.COMPLT,
						getPointerOffset(currentSrc, ignoreLoc),
						getPointerOffset(destId, ignoreLoc));
				final Expression disjunction = ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.LOGICOR,
						basesDistinct,
						ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.LOGICAND,
								destDoesNotReachIntoSrc, srcDoesNotReachIntoDest));
				loopBody.add(new AssertStatement(ignoreLoc, disjunction));
			}

			final Expression srcAcc;
			{
				final ExpressionResult srcAccExpRes = this.getReadCall(currentSrc, charCType, hook);
				srcAcc = srcAccExpRes.getLrValue().getValue();
				loopBody.addAll(srcAccExpRes.getStatements());
				decl.addAll(srcAccExpRes.getDeclarations());
				assert srcAccExpRes.getOverapprs().isEmpty();
			}

			/* #memory_int[{ base: dest!base, offset: dest!offset + #t~offset * 3 }] :=
			 *      #memory_int[{ base: src!base, offset: src!offset + #t~offset * 3 }];  */
			{
				final List<Statement> writeCall = getWriteCall(ignoreLoc,
						LRValueFactory.constructHeapLValue(mTypeHandler, currentDest, charCType, null),
						srcAcc,
						charCType,
						true,
						hook);
				loopBody.addAll(writeCall);
			}


			/* if (#memory_int[currentSrc] == 0) { break; } */
			{
				final Expression zero =
						mTypeSizes.constructLiteralForIntegerType(ignoreLoc, charCType, BigInteger.ZERO);
				final Expression exitCondition = mExpressionTranslation.constructBinaryComparisonExpression(ignoreLoc,
						IASTBinaryExpression.op_equals,
						srcAcc,
						charCType,
						zero,
						charCType);
				final Statement exitIfNull = new IfStatement(ignoreLoc, exitCondition,
						new Statement[] { new BreakStatement(ignoreLoc) },
						new Statement[0]);
				loopBody.add(exitIfNull);
			}
		}




		// loop condition is true (we exit the loop via a conditional break)
		final Expression loopCondition = ExpressionFactory.createBooleanLiteral(ignoreLoc, true);


		final Expression loopCtrIncrement =
				mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ONE);
		final List<Statement> loop =
				constructCountingLoop(loopCondition, loopCtrAux, loopCtrIncrement, loopBody, strcpyMmDecl.getName());

		final Body procBody =
				mProcedureManager.constructBody(ignoreLoc, decl.toArray(new VariableDeclaration[decl.size()]),
						loop.toArray(new Statement[loop.size()]), strcpyMmDecl.getName());

		// make the specifications
		final ArrayList<Specification> specs = new ArrayList<>();

		/* free ensures #res == dest; (this is done instead of a return statement, took this from memcpy/memmove, not
		 * sure why we are not using a return statement) */
		final EnsuresSpecification returnValue =
				mProcedureManager.constructEnsuresSpecification(
						ignoreLoc, true, ExpressionFactory.newBinaryExpression(ignoreLoc, Operator.COMPEQ,
								ExpressionFactory.constructIdentifierExpression(ignoreLoc,
										mTypeHandler.getBoogiePointerType(), SFO.RES,
										new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM,
												strcpyMmDecl.getName())),
								ExpressionFactory
										.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(),
												SFO.MEMCPY_DEST, new DeclarationInformation(
														StorageClass.PROC_FUNC_INPARAM, strcpyMmDecl.getName()))),
						Collections.emptySet());
		specs.add(returnValue);

		// add the procedure declaration
		mProcedureManager.addSpecificationsToCurrentProcedure(specs);

		// add the procedure implementation
		final Procedure strCpyProc = new Procedure(ignoreLoc, new Attribute[0], strcpyMmDecl.getName(),
				new String[0], inParams, outParams, null, procBody);
		strCpyDecl.add(strCpyProc);

		mProcedureManager.endCustomProcedure(main, strcpyMmDecl.getName());

		return strCpyDecl;
	}

	/**
	 * Construct a requires-clause that states that {@link SFO#MEMCPY_SRC} and {@link SFO#MEMCPY_DEST} do not overlap.
	 * The clause is marked as {@link Check} for {@link Spec#UNDEFINED_BEHAVIOR}.
	 *
	 * @param loc
	 *            The location of all expressions used in this requires-clause
	 * @param sizeIdExpr
	 *            an identifier expression pointing to the size variable that determines the interval of
	 *            {@link SFO#MEMCPY_SRC} that should not overlap with {@link SFO#MEMCPY_DEST}.
	 */
	private RequiresSpecification constructRequiresSourceDestNoOverlap(final ILocation loc,
			final IdentifierExpression sizeIdExpr) {
		// memcpy does not allow overlapping:
		// add requires dest.base != src.base || src.offset + size < dest.offset || dest.offset + size < src.offset
		final List<Expression> noOverlapExprs = new ArrayList<>(3);
		final IdentifierExpression srcpointer =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(),
						SFO.MEMCPY_SRC, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, SFO.MEMCPY));
		final IdentifierExpression destpointer =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(),
						SFO.MEMCPY_DEST, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, SFO.MEMCPY));
		final Expression srcbase = getPointerBaseAddress(srcpointer, loc);
		final Expression destbase = getPointerBaseAddress(destpointer, loc);
		final Expression srcoffset = getPointerOffset(srcpointer, loc);
		final Expression destoffset = getPointerOffset(destpointer, loc);

		// dest.base != src.base
		noOverlapExprs.add(ExpressionFactory.newBinaryExpression(loc, Operator.COMPNEQ, srcbase, destbase));
		// src.offset + size < dest.offset

		noOverlapExprs.add(constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessThan,
				constructPointerBinaryArithmeticExpression(loc, IASTBinaryExpression.op_plus, srcoffset, sizeIdExpr),
				destoffset));

		// dest.offset + size < src.offset
		noOverlapExprs.add(constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessThan,
				constructPointerBinaryArithmeticExpression(loc, IASTBinaryExpression.op_plus, destoffset, sizeIdExpr),
				srcoffset));

		// || over all three
		final RequiresSpecification noOverlapping =
				new RequiresSpecification(loc, false, ExpressionFactory.or(loc, noOverlapExprs));
		new Check(Spec.UNDEFINED_BEHAVIOR).annotate(noOverlapping);
		return noOverlapping;
	}

	/**
	 * Construct loop of the following form, where loopBody is a List of statements and the variables loopConterVariable
	 * and loopBoundVariable have the translated type of size_t.
	 *
	 * loopConterVariable := 0; while (condition) { ___loopBody___ loopConterVariable :=
	 * loopConterVariable + 1; }
	 *
	 * @param condition (may depend on
	 * @param loopCounterVariableId
	 * @param loopBody
	 * @return
	 */
	private ArrayList<Statement> constructCountingLoop(final Expression condition,
			final AuxVarInfo loopCounterAux, final Expression loopCounterIncrementExpr, final List<Statement> loopBody,
			final String surroundingProcedure) {
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

	/**
	 * Return the assignments that we do in the loop body of our memcpy, memmove or strcpy implementation.
	 *
	 *
	 * background: C11 7.24.2.1.2
	 * The memcpy function copies n characters from the object pointed to by s2 into the object pointed to by s1.
	 *
	 * @param heapDataArrays
	 * @param loopCtr
	 * @param destPtrName
	 * @param srcPtrName
	 * @param valueType determines which type the pointers have (thus in which steps we have to increment the access
	 *    source and destination)
	 * @return
	 */
	private ExpressionResult constructMemcpyOrMemmoveLoopAssignment(
			final Collection<HeapDataArray> heapDataArrays, final AuxVarInfo loopCtrAux, final String destPtrName,
			final String srcPtrName, final String surroundingProcedure, final IASTNode hook) {

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final CType charCType = new CPrimitive(CPrimitives.CHAR);
		final Expression srcId = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogiePointerType(), srcPtrName,
						new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, surroundingProcedure));
		final Expression destId = ExpressionFactory.constructIdentifierExpression(ignoreLoc,
				mTypeHandler.getBoogiePointerType(), destPtrName,
						new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, surroundingProcedure));


		final ExpressionResultBuilder loopBody = new ExpressionResultBuilder();
		{
			final Expression currentSrc = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, srcId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					charCType, hook);
			final Expression currentDest = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, destId,
					new RValue(loopCtrAux.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
					charCType, hook);

			for (final CPrimitives cPrim : mRequiredMemoryModelFeatures.getDataOnHeapRequired()) {
				final CType cPrimType = new CPrimitive(cPrim);
				final Expression srcAcc;
				{
					final ExpressionResult srcAccExpRes = this.getReadCall(currentSrc, cPrimType, hook);
					srcAcc = srcAccExpRes.getLrValue().getValue();
					loopBody.addStatements(srcAccExpRes.getStatements());
					loopBody.addDeclarations(srcAccExpRes.getDeclarations());
					assert srcAccExpRes.getOverapprs().isEmpty();
				}

				{
					final List<Statement> writeCall = getWriteCall(ignoreLoc,
							LRValueFactory.constructHeapLValue(mTypeHandler, currentDest, cPrimType, null),
							srcAcc,
							cPrimType,
							true,
							hook);
					loopBody.addStatements(writeCall);
				}
			}
		}

		return loopBody.build();
	}

	private ArrayList<Statement> constructMemsetLoopBody(final Collection<HeapDataArray> heapDataArrays,
			final AuxVarInfo loopCtr, final String ptr, final Expression valueExpr,
			final String surroundingProcedureName, final IASTNode hook) {

		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ArrayList<Statement> result = new ArrayList<>();


		final IdentifierExpression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogiePointerType(), ptr,
						new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, surroundingProcedureName));

		final Expression currentPtr = doPointerArithmetic(IASTBinaryExpression.op_plus, ignoreLoc, ptrExpr,
				new RValue(loopCtr.getExp(), mExpressionTranslation.getCTypeOfPointerComponents()),
				new CPrimitive(CPrimitives.VOID), hook);
		for (final HeapDataArray hda : heapDataArrays) {
			final Expression convertedValue;
			ExpressionResult exprRes = new ExpressionResult(new RValue(valueExpr, new CPrimitive(CPrimitives.UCHAR)));
			if (hda.getName().equals(SFO.POINTER)) {
				exprRes = mExpressionTranslation.convertIntToInt(ignoreLoc, exprRes,
						mExpressionTranslation.getCTypeOfPointerComponents());
				final Expression zero = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
						mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
				convertedValue = constructPointerFromBaseAndOffset(zero, exprRes.getLrValue().getValue(), ignoreLoc);
			} else {
				// convert to smallest
				final List<ReadWriteDefinition> rwds =
						mMemoryModel.getReadWriteDefinitionForHeapDataArray(hda, getRequiredMemoryModelFeatures());
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
	private CPrimitives getCprimitiveThatFitsBest(final List<ReadWriteDefinition> test) {
		int smallestBytesize = Integer.MAX_VALUE;
		for (final ReadWriteDefinition rwd : test) {
			if (rwd.getBytesize() < smallestBytesize) {
				smallestBytesize = rwd.getBytesize();
			}
		}
		if (smallestBytesize == 0) {
			// we only have unbounded data types
			return CPrimitives.UCHAR;
		}
		for (final CPrimitives primitive : new CPrimitives[] { CPrimitives.UCHAR, CPrimitives.USHORT, CPrimitives.UINT,
				CPrimitives.ULONG, CPrimitives.ULONGLONG }) {
			if (mTypeSizes.getSize(primitive) == smallestBytesize) {
				return primitive;
			}
		}
		throw new AssertionError("don't know how to store value on heap");
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
				CPrimitives.ULONG, CPrimitives.ULONGLONG }) {
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
	private List<Declaration> declareMemset(final CHandler main, final Collection<HeapDataArray> heapDataArrays,
			final IASTNode hook) {
		final ArrayList<Declaration> decls = new ArrayList<>();
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final String inParamPtr = "#ptr";
		final String inParamValue = "#value";
		final String inParamAmount = "#amount";
		final String outParamResult = "#res";
		final String procName = MemoryModelDeclarations.C_Memset.getName();

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
				constructMemsetLoopBody(heapDataArrays, loopCtrAux, inParamPtr, convertedValue, procName, hook);

		final Expression one = mTypeSizes.constructLiteralForIntegerType(ignoreLoc,
				mTypeSizeAndOffsetComputer.getSizeT(), BigInteger.ONE);
		final IdentifierExpression inParamAmountExprImpl =
				ExpressionFactory.constructIdentifierExpression(ignoreLoc, mTypeHandler.getBoogieTypeForSizeT(),
						inParamAmount, new DeclarationInformation(StorageClass.IMPLEMENTATION_INPARAM, procName));

		final List<Statement> stmt = constructCountingLoop(
				constructBoundExitCondition(inParamAmountExprImpl, loopCtrAux), loopCtrAux, one, loopBody, procName);

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
			final Collection<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray, final IASTNode hook) {
		final List<Declaration> result = new ArrayList<>();
		for (final ReadWriteDefinition rda : mMemoryModel.getReadWriteDefinitionForHeapDataArray(heapDataArray,
				mRequiredMemoryModelFeatures)) {
			final Collection<Procedure> writeDeclaration =
					constructWriteProcedure(main, loc, heapDataArrays, heapDataArray, rda, hook);
			result.addAll(writeDeclaration);
		}
		return result;
	}

	private List<Declaration> constructReadProcedures(final CHandler main, final ILocation loc,
			final HeapDataArray heapDataArray, final IASTNode hook) {
		final List<Declaration> result = new ArrayList<>();
		for (final ReadWriteDefinition rda : mMemoryModel.getReadWriteDefinitionForHeapDataArray(heapDataArray,
				mRequiredMemoryModelFeatures)) {
			final List<Procedure> readDeclaration = constructReadProcedure(main, loc, heapDataArray, rda, hook);
			result.addAll(readDeclaration);
		}
		return result;
	}

	private VariableDeclaration declarePThreadsMutexArray(final ILocation loc) {
		final String arrayName = SFO.ULTIMATE_PTHREADS_MUTEX;
		return constructDeclOfPointerIndexedArray(loc, mBooleanArrayHelper.constructBoolReplacementType(), arrayName);
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
			final ReadWriteDefinition rda, final IASTNode hook) {
		if (rda.alsoUnchecked()) {
			constructSingleWriteProcedure(main, loc, heapDataArrays, heapDataArray, rda, HeapWriteMode.Store_Unchecked);
		}
		if (rda.alsoInit()) {
			constructSingleWriteProcedure(main, loc, heapDataArrays, heapDataArray, rda, HeapWriteMode.Select);
		}
		constructSingleWriteProcedure(main, loc, heapDataArrays, heapDataArray, rda, HeapWriteMode.Store_Checked);
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
		case Select:
			procName = rda.getInitWriteProcedureName();
			break;
		case Store_Checked:
			procName = rda.getWriteProcedureName();
			break;
		case Store_Unchecked:
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
		if (writeMode == HeapWriteMode.Store_Checked) {
			swrite.addAll(constructPointerBaseValidityCheck(loc, inPtr, procName));

			final Expression sizeWrite = ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT,
					writtenTypeSize, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procName));
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

		final boolean useSelectInsteadOfStore = writeMode == HeapWriteMode.Select;

		final List<Expression> conjuncts = new ArrayList<>();
		if (rda.getBytesize() == heapDataArray.getSize()) {
			conjuncts.addAll(constructConjunctsForWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray,
					returnValue, x -> x, inPtrExp, x -> x, useSelectInsteadOfStore));
		} else if (rda.getBytesize() < heapDataArray.getSize()) {
			final Function<Expression, Expression> valueExtension =
					x -> mExpressionTranslation.signExtend(loc, x, rda.getBytesize() * 8, heapDataArray.getSize() * 8);
			conjuncts.addAll(constructConjunctsForWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray,
					returnValue, valueExtension, inPtrExp, x -> x, useSelectInsteadOfStore));
		} else {
			assert rda.getBytesize() % heapDataArray.getSize() == 0 : "incompatible sizes";
			for (int i = 0; i < rda.getBytesize() / heapDataArray.getSize(); i++) {
				final Function<Expression, Expression> extractBits;
				final int currentI = i;
				extractBits = x -> mExpressionTranslation.extractBits(loc, x,
						heapDataArray.getSize() * (currentI + 1) * 8, heapDataArray.getSize() * currentI * 8);
				if (i == 0) {
					conjuncts.addAll(constructConjunctsForWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray,
							returnValue, extractBits, inPtrExp, x -> x, useSelectInsteadOfStore));
				} else {
					final BigInteger additionalOffset = BigInteger.valueOf(i * heapDataArray.getSize());
					final Function<Expression, Expression> pointerAddition =
							x -> addIntegerConstantToPointer(loc, x, additionalOffset);
					conjuncts.addAll(constructConjunctsForWriteEnsuresSpecification(loc, heapDataArrays, heapDataArray,
							returnValue, extractBits, inPtrExp, pointerAddition, useSelectInsteadOfStore));
				}
			}
		}

		final Set<VariableLHS> modifiedGlobals = useSelectInsteadOfStore ?
				Collections.emptySet() :
					heapDataArrays.stream().map(hda -> hda.getVariableLHS()).collect(Collectors.toSet());

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
			swrite.add(mProcedureManager.constructEnsuresSpecification(loc, false, qe,
					modifiedGlobals));
		} else {
			swrite.add(mProcedureManager.constructEnsuresSpecification(loc, false,
					ExpressionFactory.and(loc, conjuncts), modifiedGlobals));
		}

		mProcedureManager.addSpecificationsToCurrentProcedure(swrite);
		mProcedureManager.endCustomProcedure(main, procName);
	}

	private static List<Expression> constructConjunctsForWriteEnsuresSpecification(final ILocation loc,
			final Collection<HeapDataArray> heapDataArrays, final HeapDataArray heapDataArray, final Expression value,
			final Function<Expression, Expression> valueModification, final IdentifierExpression inPtrExp,
			final Function<Expression, Expression> ptrModification, final boolean useSelectInsteadOfStore) {
		final List<Expression> conjuncts = new ArrayList<>();
		for (final HeapDataArray other : heapDataArrays) {
			if (heapDataArray == other) {
				conjuncts.add(constructHeapArrayUpdateForWriteEnsures(loc, value, valueModification, inPtrExp,
						ptrModification, other, useSelectInsteadOfStore));
			} else {
				if (useSelectInsteadOfStore) {
					// do nothing (no need to havoc an uninitialized memory cell)
				} else {
					conjuncts.add(constructHeapArrayHardlyModifiedForWriteEnsures(loc, inPtrExp, ptrModification,
							other));
				}
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
	 * @return
	 */
	private List<Procedure> constructReadProcedure(final CHandler main, final ILocation loc, final HeapDataArray hda,
			final ReadWriteDefinition rda, final IASTNode hook) {
		// specification for memory reads
		final String returnValue = "#value";
		final ASTType valueAstType = rda.getASTType();
		final String ptrId = "#ptr";
		final String readTypeSize = "#sizeOfReadType";

		// create procedure signature
		{
			final ASTType sizetType = mTypeHandler.cType2AstType(loc, mTypeSizeAndOffsetComputer.getSizeT());
			final VarList[] inRead =
					new VarList[] { new VarList(loc, new String[] { ptrId }, mTypeHandler.constructPointerType(loc)),
							new VarList(loc, new String[] { readTypeSize }, sizetType) };

			final VarList[] outRead = new VarList[] { new VarList(loc, new String[] { returnValue }, valueAstType) };
			final Procedure decl = new Procedure(loc, new Attribute[0], rda.getReadProcedureName(), new String[0],
					inRead, outRead, new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, loc, rda.getReadProcedureName(), decl);
		}

		// create procedure specifications
		final ArrayList<Specification> sread = new ArrayList<>();

		sread.addAll(constructPointerBaseValidityCheck(loc, ptrId, rda.getReadProcedureName()));

		final Expression sizeRead = ExpressionFactory.constructIdentifierExpression(loc, BoogieType.TYPE_INT,
				readTypeSize, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, rda.getReadProcedureName()));

		sread.addAll(constructPointerTargetFullyAllocatedCheck(loc, sizeRead, ptrId, rda.getReadProcedureName()));

		final Expression arr = hda.getIdentifierExpression();
		final Expression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrId,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, rda.getReadProcedureName()));

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
				new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, rda.getReadProcedureName()));
		final Expression equality =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, valueExpr, dataFromHeap);
		sread.add(mProcedureManager.constructEnsuresSpecification(loc, false, equality, Collections.emptySet()));

		mProcedureManager.addSpecificationsToCurrentProcedure(sread);
		mProcedureManager.endCustomProcedure(main, rda.getReadProcedureName());

		return Collections.emptyList();
	}

	private Expression addIntegerConstantToPointer(final ILocation loc, final Expression ptrExpr,
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

	// ensures #memory_X == old(#memory_X)[#ptr := #value];
	private static Expression constructHeapArrayUpdateForWriteEnsures(final ILocation loc, final Expression valueExpr,
			final Function<Expression, Expression> valueModification, final IdentifierExpression ptrExpr,
			final Function<Expression, Expression> ptrModification, final HeapDataArray hda,
			final boolean useSelectInsteadOfStore) {
		final Expression memArray = hda.getIdentifierExpression();
		if (useSelectInsteadOfStore) {
			return ensuresArrayHasValue(loc, valueModification.apply(valueExpr), ptrModification.apply(ptrExpr),
					memArray);
		} else {
			return ensuresArrayUpdate(loc, valueModification.apply(valueExpr), ptrModification.apply(ptrExpr),
					memArray);
		}
	}

	// #memory_$Pointer$ == old(#memory_X)[#ptr := #memory_X[#ptr]];
	private static Expression constructHeapArrayHardlyModifiedForWriteEnsures(final ILocation loc,
			final IdentifierExpression ptrExpr, final Function<Expression, Expression> ptrModification,
			final HeapDataArray hda) {
		final Expression memArray = hda.getIdentifierExpression();
		final Expression aae = constructOneDimensionalArrayAccess(loc, memArray, ptrExpr);
		return ensuresArrayUpdate(loc, aae, ptrModification.apply(ptrExpr), memArray);
	}

	/**
	 *  arr == old(arr)[index := newValue]
	 */
	private static Expression ensuresArrayUpdate(final ILocation loc, final Expression newValue, final Expression index,
			final Expression arrayExpr) {
		final Expression oldArray =
				ExpressionFactory.constructUnaryExpression(loc, UnaryExpression.Operator.OLD, arrayExpr);
		final Expression ase = constructOneDimensionalArrayStore(loc, oldArray, index, newValue);
		final Expression eq = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, arrayExpr, ase);
		return eq;
	}

	/**
	 *  arr[index] == value
	 */
	private static Expression ensuresArrayHasValue(final ILocation loc, final Expression value, final Expression index,
			final Expression arrayExpr) {
		final Expression select = ExpressionFactory.constructNestedArrayAccessExpression(loc, arrayExpr,
				new Expression[] { index });
		final Expression eq = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, select, value);
		return eq;
	}

	/**
	 *
	 * @param loc
	 *            location of translation unit
	 * @param vars
	 * @return ModifiesSpecification which says that all variables of the set vars can be modified.
	 */
	private static <T> ModifiesSpecification constructModifiesSpecification(final ILocation loc,
			final Collection<T> vars, final Function<T, VariableLHS> varToLHS) {
		final VariableLHS[] modifie = new VariableLHS[vars.size()];
		int i = 0;
		for (final T variable : vars) {
			modifie[i] = varToLHS.apply(variable);
			i++;
		}
		return new ModifiesSpecification(loc, false, modifie);
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
	private List<Specification> constructPointerTargetFullyAllocatedCheck(final ILocation loc, final Expression size,
			final String ptrName, final String procedureName) {
		if (mSettings.getPointerTargetFullyAllocatedMode() == PointerCheckMode.IGNORE) {
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
		if (mSettings.getPointerTargetFullyAllocatedMode() == PointerCheckMode.ASSERTandASSUME) {
			isFreeRequires = false;
		} else {
			assert mSettings.getPointerTargetFullyAllocatedMode() == PointerCheckMode.ASSUME;
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
	private List<Specification> constructPointerBaseValidityCheck(final ILocation loc, final String ptrName,
			final String procedureName) {
		if (mSettings.getPointerBaseValidityMode() == PointerCheckMode.IGNORE) {
			// add nothing
			return Collections.emptyList();
		}
		final Expression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));
		final Expression isValid = constructPointerBaseValidityCheckExpr(loc, ptrExpr);
		final boolean isFreeRequires;
		if (mSettings.getPointerBaseValidityMode() == PointerCheckMode.ASSERTandASSUME) {
			isFreeRequires = false;
		} else {
			assert mSettings.getPointerBaseValidityMode() == PointerCheckMode.ASSUME;
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
	 * @return declaration and implementation of procedure <code>Ultimate_dealloc</code>
	 */
	private List<Declaration> declareDeallocation(final CHandler main, final ILocation tuLoc, final IASTNode hook) {
		final Expression bLFalse = mBooleanArrayHelper.constructFalse();
		final Expression addr = ExpressionFactory.constructIdentifierExpression(tuLoc,
				mTypeHandler.getBoogiePointerType(), ADDR, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM,
						MemoryModelDeclarations.Ultimate_Dealloc.getName()));
		final Expression valid = getValidArray(tuLoc);
		final Expression addrBase = ExpressionFactory.constructStructAccessExpression(tuLoc, addr, SFO.POINTER_BASE);
		final Expression[] idcFree = new Expression[] { addrBase };

		{
			final Procedure deallocDeclaration = new Procedure(tuLoc, new Attribute[0],
					MemoryModelDeclarations.Ultimate_Dealloc.getName(), new String[0],
					new VarList[] {
							new VarList(tuLoc, new String[] { ADDR }, mTypeHandler.constructPointerType(tuLoc)) },
					new VarList[0], new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, tuLoc, MemoryModelDeclarations.Ultimate_Dealloc.getName(),
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
		mProcedureManager.endCustomProcedure(main, MemoryModelDeclarations.Ultimate_Dealloc.getName());
		return Collections.emptyList();
	}

	/**
	 * Generate <code>procedure ~Ultimate.alloc(~size:int) returns (#res:$Pointer$);</code>'s declaration and
	 * implementation.
	 *
	 * @param typeHandler
	 *
	 * @param tuLoc
	 *            the location for the new nodes.
	 * @return declaration and implementation of procedure <code>~malloc</code>
	 */
	private ArrayList<Declaration> declareMalloc(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc, final IASTNode hook) {
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
						new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM,
								MemoryModelDeclarations.Ultimate_Alloc.getName()));

		final Expression length = getLengthArray(tuLoc);
		// #res!base
		final Expression resBase = ExpressionFactory.constructStructAccessExpression(tuLoc, res, SFO.POINTER_BASE);
		// { #res!base }
		final Expression[] idcMalloc = new Expression[] { resBase };
		final Expression bLTrue = mBooleanArrayHelper.constructTrue();
		final Expression bLFalse = mBooleanArrayHelper.constructFalse();
		// ~size
		final IdentifierExpression size = // new IdentifierExpression(tuLoc, SIZE);
				ExpressionFactory.constructIdentifierExpression(tuLoc, BoogieType.TYPE_INT, SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM,
								MemoryModelDeclarations.Ultimate_Alloc.getName()));

		{
			final Procedure allocDeclaration = new Procedure(tuLoc, new Attribute[0],
					MemoryModelDeclarations.Ultimate_Alloc.getName(), new String[0],
					new VarList[] { new VarList(tuLoc, new String[] { SIZE }, intType) },
					new VarList[] {
							new VarList(tuLoc, new String[] { SFO.RES }, typeHandler.constructPointerType(tuLoc)) },
					new Specification[0], null);
			mProcedureManager.beginCustomProcedure(main, tuLoc, MemoryModelDeclarations.Ultimate_Alloc.getName(),
					allocDeclaration);
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
			final Expression addr = ExpressionFactory.constructIdentifierExpression(tuLoc,
					mTypeHandler.getBoogiePointerType(), ADDR,
					new DeclarationInformation(StorageClass.LOCAL, MemoryModelDeclarations.Ultimate_Alloc.getName()));
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
							new DeclarationInformation(StorageClass.IMPLEMENTATION_OUTPARAM,
									MemoryModelDeclarations.Ultimate_Alloc.getName()));
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

			final Body bodyMalloc = mProcedureManager.constructBody(tuLoc, localVars, block,
					MemoryModelDeclarations.Ultimate_Alloc.getName());
			result.add(new Procedure(tuLoc, new Attribute[0], MemoryModelDeclarations.Ultimate_Alloc.getName(),
					new String[0], new VarList[] { new VarList(tuLoc, new String[] { SIZE }, intType) },
					new VarList[] {
							new VarList(tuLoc, new String[] { SFO.RES }, typeHandler.constructPointerType(tuLoc)) },
					null, bodyMalloc));
		}
		mProcedureManager.endCustomProcedure(main, MemoryModelDeclarations.Ultimate_Alloc.getName());
		return result;
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
			final CArray valueType, final HeapWriteMode writeMode, final IASTNode hook) {

		if (valueType.getValueType().getUnderlyingType() instanceof CArray) {
			throw new UnsupportedSyntaxException(loc,
					"we need to generalize this to nested and/or variable length arrays");
		}

		final BigInteger dimBigInteger = mTypeSizes.extractIntegerValue(valueType.getBound(), hook);
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

		final Expression valueTypeSize = calculateSizeOf(loc, valueType.getValueType(), hook);
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
					writeMode, hook));
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
			final CStructOrUnion valueType, final HeapWriteMode writeMode, final IASTNode hook) {
		final List<Statement> stmt = new ArrayList<>();
		for (final String fieldId : valueType.getFieldIds()) {
			final Expression startAddress = hlv.getAddress();
			final Expression newStartAddressBase = MemoryHandler.getPointerBaseAddress(startAddress, loc);
			final Expression newStartAddressOffset = MemoryHandler.getPointerOffset(startAddress, loc);
			final CType fieldType = valueType.getFieldType(fieldId);
			final StructAccessExpression sae = ExpressionFactory.constructStructAccessExpression(loc, value, fieldId);
			final Expression fieldOffset =
					mTypeSizeAndOffsetComputer.constructOffsetForField(loc, valueType, fieldId, hook);
			final Expression newOffset =
					mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
							newStartAddressOffset, mExpressionTranslation.getCTypeOfPointerComponents(), fieldOffset,
							mExpressionTranslation.getCTypeOfPointerComponents());
			final HeapLValue fieldHlv = LRValueFactory.constructHeapLValue(mTypeHandler,
					constructPointerFromBaseAndOffset(newStartAddressBase, newOffset, loc), fieldType, null);
			stmt.addAll(getWriteCall(loc, fieldHlv, sae, fieldType, writeMode, hook));
		}
		return stmt;
	}

	private List<Statement> getWriteCallPointer(final ILocation loc, final HeapLValue hlv, final Expression value,
			final HeapWriteMode writeMode, final IASTNode hook) {
		mRequiredMemoryModelFeatures.reportPointerOnHeapRequired();
		final String writeCallProcedureName = determineWriteProcedureForPointer(writeMode);// mMemoryModel.getWritePointerProcedureName();
		return Collections.singletonList(
				StatementFactory.constructCallStatement(loc, false, new VariableLHS[0], writeCallProcedureName,
						new Expression[] { value, hlv.getAddress(), calculateSizeOf(loc, hlv.getCType(), hook) }));
	}

	private String determineWriteProcedureForPointer(final HeapWriteMode writeMode)
			throws AssertionError {
		final String writeCallProcedureName;
		switch (writeMode) {
		case Select:
			mRequiredMemoryModelFeatures.reportPointerInitWriteRequired();
			writeCallProcedureName = mMemoryModel.getInitPointerProcedureName();
			break;
		case Store_Checked:
			writeCallProcedureName = mMemoryModel.getWritePointerProcedureName();
			break;
		case Store_Unchecked:
			mRequiredMemoryModelFeatures.reportPointerUncheckedWriteRequired();
			writeCallProcedureName = mMemoryModel.getUncheckedWritePointerProcedureName();
			break;
		default:
			throw new AssertionError("todo: add new enum case");
		}
		return writeCallProcedureName;
	}

	private List<Statement> getWriteCallEnum(final ILocation loc, final HeapLValue hlv, final Expression value,
			final HeapWriteMode writeMode, final IASTNode hook) {
		// treat like INT
		return getWriteCallPrimitive(loc, hlv, value, new CPrimitive(CPrimitives.INT), writeMode, hook);
	}

	private List<Statement> getWriteCallPrimitive(final ILocation loc, final HeapLValue hlv, final Expression value,
			final CPrimitive valueType, final HeapWriteMode writeMode, final IASTNode hook) {
		checkFloatOnHeapSupport(loc, valueType);
		mRequiredMemoryModelFeatures.reportDataOnHeapRequired(valueType.getType());

		final String writeCallProcedureName = determineWriteProcedureForPrimitive(valueType, writeMode);

		return Collections.singletonList(
				StatementFactory.constructCallStatement(loc, false, new VariableLHS[0], writeCallProcedureName,
						new Expression[] { value, hlv.getAddress(), calculateSizeOf(loc, hlv.getCType(), hook) }));
	}

	private String determineWriteProcedureForPrimitive(final CPrimitive valueType, final HeapWriteMode writeMode)
			throws AssertionError {
		final String writeCallProcedureName;
		switch (writeMode) {
		case Select:
			mRequiredMemoryModelFeatures.reportInitWriteRequired(valueType.getType());
			writeCallProcedureName = mMemoryModel.getInitWriteProcedureName(valueType.getType());
			break;
		case Store_Checked:
			writeCallProcedureName = mMemoryModel.getWriteProcedureName(valueType.getType());
			break;
		case Store_Unchecked:
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
		case C_Memcpy:
			break;
		case C_Memmove:
			break;
		case C_Memset:
			break;
		case Ultimate_Alloc:
			break;
		case Ultimate_Dealloc:
			break;
		case Ultimate_Length:
			return new MemoryModelDeclarationInfo(mmd, BoogieType.createArrayType(0,
					new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() }, BoogieType.TYPE_INT));
		case Ultimate_MemInit:
			break;
		case Ultimate_Pthreads_Mutex:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogiePointerType() }, mTypeHandler
							.getBoogieTypeForBoogieASTType(getBooleanArrayHelper().constructBoolReplacementType())));
		case Ultimate_Valid:
			return new MemoryModelDeclarationInfo(mmd,
					BoogieType.createArrayType(0, new BoogieType[] { mTypeHandler.getBoogieTypeForPointerComponents() },
							mTypeHandler.getBoogieTypeForBoogieASTType(
									getBooleanArrayHelper().constructBoolReplacementType())));
		default:
			break;
		}
		// construct empty mmdi
		return new MemoryModelDeclarationInfo(mmd);
	}

	/**
	 * We assume that the mutex type is PTHREAD_MUTEX_NORMAL which means that if we
	 * lock a mutex that that is already locked, then the thread blocks.
	 */
	private ArrayList<Declaration> declarePthreadMutexLock(final CHandler main, final ITypeHandler typeHandler,
			final ILocation tuLoc, final IASTNode hook) {
		final String inputPointerIdentifier = "#inputPtr";
		final ASTType inputPointerAstType = typeHandler.cType2AstType(tuLoc,
				new CPointer(new CPrimitive(CPrimitives.VOID)));
		final String resultIdentifier = SFO.RES;
		final CType resultCType = new CPrimitive(CPrimitives.INT);
		final ASTType resultAstType = typeHandler.cType2AstType(tuLoc, resultCType);
		final BoogieType resultBoogieType = typeHandler.getBoogieTypeForCType(resultCType);

		final Expression nr0 = mTypeSizes.constructLiteralForIntegerType(tuLoc, new CPrimitive(CPrimitives.INT),
				BigInteger.ZERO);
		final Expression inputPointerExpression = ExpressionFactory.constructIdentifierExpression(tuLoc,
				mTypeHandler.getBoogiePointerType(), inputPointerIdentifier,
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM,
						MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK.getName()));

		final Expression resultIdentifierExpression = ExpressionFactory.constructIdentifierExpression(tuLoc,
				resultBoogieType, resultIdentifier, new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM,
						MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK.getName()));

		final Expression mutexArray = constructMutexArrayIdentifierExpression(tuLoc);
		final Expression bLTrue = mBooleanArrayHelper.constructTrue();
		final Expression bLFalse = mBooleanArrayHelper.constructFalse();

		final Procedure procDecl = new Procedure(tuLoc, new Attribute[0],
				MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK.getName(), new String[0],
				new VarList[] { new VarList(tuLoc, new String[] { inputPointerIdentifier }, inputPointerAstType) },
				new VarList[] { new VarList(tuLoc, new String[] { resultIdentifier }, resultAstType) },
				new Specification[0], null);
		mProcedureManager.beginCustomProcedure(main, tuLoc,
				MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK.getName(), procDecl);

		final List<Specification> specs = new ArrayList<>();

		// old(#PthreadsMutex)[#ptr] == false
		specs.add(mProcedureManager.constructEnsuresSpecification(tuLoc, true,
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
						ExpressionFactory.constructNestedArrayAccessExpression(tuLoc,
								ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD,
										mutexArray),
								new Expression[] { inputPointerExpression }),
						bLFalse),
				Collections.emptySet()));
		// #PthreadsMutex == old(#PthreadsMutex)[#ptr := true]
		specs.add(mProcedureManager.constructEnsuresSpecification(tuLoc, true,
				ensuresArrayUpdate(tuLoc, bLTrue, inputPointerExpression, mutexArray),
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(mutexArray))));

		// we assume that function is always successful and returns 0
		// #res == 0
		specs.add(mProcedureManager.constructEnsuresSpecification(tuLoc, true,
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, resultIdentifierExpression, nr0),
				Collections.emptySet()));
		mProcedureManager.addSpecificationsToCurrentProcedure(specs);

		final ArrayList<Declaration> result = new ArrayList<>();
		mProcedureManager.endCustomProcedure(main, MemoryModelDeclarations.ULTIMATE_PTHREADS_MUTEX_LOCK.getName());
//		result.add(procDecl);
		return result;
	}

	/**
	 * Sets the heap at the given base address to all 0s.
	 * Analyzes the given type to check which heap arrays should be updated.
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
		assert CTranslationUtil.isAggregateOrUnionType(cType);

		final Set<CType> relevantBaseTypes = CTranslationUtil.extractNonAggregateNonUnionTypes(cType);

		return getInitializationForHeapAtPointer(loc, baseAddress, relevantBaseTypes);
	}

	private List<Statement> getInitializationForHeapAtPointer(final ILocation loc, final HeapLValue baseAddress,
			final Set<CType> relevantBaseTypes) throws AssertionError {
		// first collect the concerned heap arrays (in a set, to avoid duplicates)
		final Set<HeapDataArray> relevantHeapArrays = new HashSet<>();
		for (final CType baseType : relevantBaseTypes ) {
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

	private Statement getInitializationForHeapArrayAtAddress(final ILocation loc, final HeapDataArray relevantHeapArray,
			final HeapLValue baseAddress) {
		return StatementFactory.constructAssignmentStatement(loc,
				new VariableLHS[] { relevantHeapArray.getVariableLHS() },
				new Expression[] {
						ExpressionFactory.constructFunctionApplication(
								loc,
								getNameOfHeapInitFunction(relevantHeapArray),
								new Expression[] {
										relevantHeapArray.getIdentifierExpression(),
										getPointerBaseAddress(baseAddress.getAddress(), loc)
										},
								(BoogieType) relevantHeapArray.getIdentifierExpression().getType()
								)});
	}

	private String getNameOfHeapInitFunction(final HeapDataArray relevantHeapArray) {
		return SFO.AUXILIARY_FUNCTION_PREFIX + "initToZeroAtPointerBaseAddress~" + relevantHeapArray.getName();
	}

	private void declareDataOnHeapInitFunction(final HeapDataArray heapDataArray) {

		final CACSLLocation ignoreLoc = LocationFactory.createIgnoreCLocation();

		final List<Attribute> attributeList = new ArrayList<>();

		final CPrimitive cTypeOfPointerComponents = mExpressionTranslation.getCTypeOfPointerComponents();
		final ASTType astTypeOfPointerComponents = mTypeHandler.cType2AstType(ignoreLoc, cTypeOfPointerComponents);
		final BoogieType boogieTypeOfPointerComponents =
				mTypeHandler.getBoogieTypeForBoogieASTType(astTypeOfPointerComponents);
		final String smtSortOfPointerComponents =
				CTranslationUtil.getSmtSortStringForBoogieType(boogieTypeOfPointerComponents);


		final BoogieType heapContentBoogieType = heapDataArray.getArrayContentBoogieType();
		// should not be necessary, doing just to be safe in case we add heap arrays with more complicated types
		final BoogieType flattenedType = StructExpanderUtil.flattenType(heapContentBoogieType, new HashMap<>(), new HashMap<>());

		if (flattenedType instanceof BoogieStructType) {
			final BoogieStructType bst = (BoogieStructType) flattenedType;

			for (int fieldNr = 0; fieldNr < bst.getFieldCount(); fieldNr++) {

				// add expand attribute
				final NamedAttribute expandAttribute = new NamedAttribute(
						ignoreLoc,
						StructExpanderUtil.ATTRIBUTE_EXPAND_STRUCT,
						new Expression[] {
								ExpressionFactory.createStringLiteral(ignoreLoc, bst.getFieldIds()[fieldNr])
						});
				attributeList.add(expandAttribute);

				final String zero = CTranslationUtil.getSmtZeroStringForBoogieType(bst.getFieldType(fieldNr));

				final String contentType = CTranslationUtil.getSmtSortStringForBoogieType(bst.getFieldType(fieldNr));

				final String smtDefinition = String.format("(store %s %s ((as const (Array %s %s)) %s))",
						FunctionDeclarations.constructNameForFunctionInParam(0)
							+ StructExpanderUtil.DOT + bst.getFieldIds()[fieldNr],
						FunctionDeclarations.constructNameForFunctionInParam(1),
						smtSortOfPointerComponents,
						contentType,
						zero);

				final NamedAttribute namedAttribute = new NamedAttribute(
						ignoreLoc,
						FunctionDeclarations.SMTDEFINED_IDENTIFIER,
						new Expression[] {
								ExpressionFactory.createStringLiteral(ignoreLoc, smtDefinition)
						});
				attributeList.add(namedAttribute);
			}
		} else {

			final String zero = CTranslationUtil.getSmtZeroStringForBoogieType(heapContentBoogieType);
			final String contentType = CTranslationUtil.getSmtSortStringForBoogieType(heapContentBoogieType);

			final String smtDefinition = String.format("(store %s %s ((as const (Array %s %s)) %s))",
					FunctionDeclarations.constructNameForFunctionInParam(0),
					FunctionDeclarations.constructNameForFunctionInParam(1),
					smtSortOfPointerComponents,
					contentType,
					zero);

			final NamedAttribute namedAttribute = new NamedAttribute(
					ignoreLoc,
					FunctionDeclarations.SMTDEFINED_IDENTIFIER,
					new Expression[] {
							ExpressionFactory.createStringLiteral(ignoreLoc, smtDefinition)
					});
			attributeList.add(namedAttribute);
		}

		final Attribute[] attributes = attributeList.toArray(new Attribute[attributeList.size()]);

		// register the FunctionDeclaration so it will be added at the end of translation

		mExpressionTranslation.getFunctionDeclarations()
			.declareFunction(ignoreLoc,
				getNameOfHeapInitFunction(heapDataArray),
				//new Attribute[] { namedAttribute},
				attributes,
				((BoogieType) heapDataArray.getIdentifierExpression().getType()).toASTType(ignoreLoc),
				((BoogieType) heapDataArray.getIdentifierExpression().getType()).toASTType(ignoreLoc),
				astTypeOfPointerComponents
				);

	}

	/**
	 * Construct assert statements that do memsafety checks for {@link pointerValue} if the corresponding settings are
	 * active. settings concerned are: - "Pointer base address is valid at dereference" - "Pointer to allocated memory
	 * at dereference"
	 * @param loc TODO
	 * @param pointerValue TODO
	 * @param standardFunctionHandler TODO
	 * @param expressionTranslation TODO
	 */
	public List<Statement> constructMemsafetyChecksForPointerExpression(final ILocation loc,
			final Expression pointerValue) {
		final List<Statement> result = new ArrayList<>();
		if (mSettings.getPointerBaseValidityMode() != PointerCheckMode.IGNORE) {

			// valid[s.base]
			final Expression validBase = constructPointerBaseValidityCheckExpr(loc, pointerValue);

			if (mSettings.getPointerBaseValidityMode() == PointerCheckMode.ASSERTandASSUME) {
				final AssertStatement assertion = new AssertStatement(loc, validBase);
				final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
				chk.annotate(assertion);
				result.add(assertion);
			} else {
				assert mSettings.getPointerBaseValidityMode() == PointerCheckMode.ASSUME : "missed a case?";
				final Statement assume = new AssumeStatement(loc, validBase);
				result.add(assume);
			}
		}
		if (mSettings.getPointerTargetFullyAllocatedMode() != PointerCheckMode.IGNORE) {

			// s.offset < length[s.base])
			final Expression offsetSmallerLength = mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc,
					IASTBinaryExpression.op_lessThan, MemoryHandler.getPointerOffset(pointerValue, loc),
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
			if (mSettings.getPointerBaseValidityMode() == PointerCheckMode.ASSERTandASSUME) {
				final AssertStatement assertion = new AssertStatement(loc, aAndB);
				final Check chk = new Check(Spec.MEMORY_DEREFERENCE);
				chk.annotate(assertion);
				result.add(assertion);
			} else {
				assert mSettings.getPointerBaseValidityMode() == PointerCheckMode.ASSUME : "missed a case?";
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

	/**
	 *
	 *
	 * Note that this class has two freezing mechanisms. (Here, freezing means that at some point we set a flag and
	 *  after that nothing may change anymore in the class members associated with the flag.)
	 * <li> One for the query if any memory model features are required (PostProcessor queries this because it needs to
	 *  know for the init procedure.).
	 * <li> At the start of {@link MemoryHandler#declareMemoryModelInfrastructure(CHandler, ILocation, IASTNode)},
	 *  the method {@link RequiredMemoryModelFeatures#finish()} is called. This method resolves dependencies between the
	 *  different memory model features (e.g. memcpy requires write_unchecked procedures for all heap data arrays),
	 *   afterwards it freezes those features.
	 *
	 * Background:
	 *  There are different dependencies between features recorded in this class.
	 *  Simple ones are resolved immediately (e.g. reportPointerUncheckedWriteRequired, triggers
	 *   reportPointerOnHeapRequired).
	 *  Others are resolved during finish().
	 */
	public static final class RequiredMemoryModelFeatures {

		/**
		 * This flag must be set if any of the memory model features are required.
		 */
		private boolean mMemoryModelInfrastructureRequired;

		private final Set<CPrimitives> mDataOnHeapRequired;
		private final Set<CPrimitives> mDataUncheckedWriteRequired;
		private final Set<CPrimitives> mDataInitWriteRequired;
		private boolean mPointerOnHeapRequired;
		private boolean mPointerUncheckedWriteRequired;
		private boolean mPointerInitWriteRequired;
		private final Set<MemoryModelDeclarations> mRequiredMemoryModelDeclarations;

		/**
		 * Set of HeapDataArrays for which constant array initialization is required.
		 * (for those we create a Boogie function with smtdefined attribute..)
		 */
		private final Set<CPrimitives> mDataOnHeapInitFunctionRequired;
		private boolean mPointerOnHeapInitFunctionRequired;

		/**
		 * Once this flag is set, no member of this class may be changed anymore.
		 */
		private boolean mIsFrozen;

		private boolean mMemoryModelInfrastructureRequiredHasBeenQueried;

		public RequiredMemoryModelFeatures() {
			mDataOnHeapRequired = new HashSet<>();
			mRequiredMemoryModelDeclarations = new HashSet<>();
			mDataUncheckedWriteRequired = new HashSet<>();
			mDataInitWriteRequired = new HashSet<>();
			mDataOnHeapInitFunctionRequired = new HashSet<>();
		}

		public boolean requireMemoryModelInfrastructure() {
			if (mMemoryModelInfrastructureRequired) {
				return false;
			}
			if (mMemoryModelInfrastructureRequiredHasBeenQueried) {
				throw new AssertionError("someone already asked if memory model infrastructure was required and we "
						+ "said no");
			}
			mMemoryModelInfrastructureRequired = true;
			require(MemoryModelDeclarations.Ultimate_Length);
			require(MemoryModelDeclarations.Ultimate_Valid);
			return true;
		}

		public boolean reportPointerOnHeapRequired() {
			if (mPointerOnHeapRequired) {
				return false;
			}
			checkNotFrozen();
			requireMemoryModelInfrastructure();
			mPointerOnHeapRequired = true;
			return true;
		}

		public boolean reportPointerUncheckedWriteRequired() {
			if (mPointerUncheckedWriteRequired) {
				return false;
			}
			checkNotFrozen();
			reportPointerOnHeapRequired();
			mPointerUncheckedWriteRequired = true;
			return true;
		}

		public boolean reportPointerInitWriteRequired() {
			if (mPointerInitWriteRequired) {
				return false;
			}
			checkNotFrozen();
			reportPointerOnHeapRequired();
			mPointerInitWriteRequired = true;
			return true;
		}

		public boolean reportDataOnHeapRequired(final CPrimitives primitive) {
			if (mDataOnHeapRequired.contains(primitive)) {
				return false;
			}
			checkNotFrozen();
			requireMemoryModelInfrastructure();
			mDataOnHeapRequired.add(primitive);
			return true;
		}

		public boolean reportUncheckedWriteRequired(final CPrimitives primitive) {
			if (mDataUncheckedWriteRequired.contains(primitive)) {
				return false;
			}
			checkNotFrozen();
			reportDataOnHeapRequired(primitive);
			mDataUncheckedWriteRequired.add(primitive);
			return true;
		}

		public boolean reportInitWriteRequired(final CPrimitives prim) {
			if (mDataInitWriteRequired.contains(prim)) {
				return false;
			}
			checkNotFrozen();
			reportDataOnHeapRequired(prim);
			mDataInitWriteRequired.add(prim);
			return true;
		}

		public boolean reportDataOnHeapInitFunctionRequired(final CPrimitives prim) {
			if (mDataOnHeapInitFunctionRequired.contains(prim)) {
				return false;
			}
			checkNotFrozen();
			reportDataOnHeapRequired(prim);
			mDataOnHeapInitFunctionRequired.add(prim);
			return true;
		}

		public boolean reportPointerOnHeapInitFunctionRequired() {
			if (mPointerOnHeapInitFunctionRequired) {
				return false;
			}
			checkNotFrozen();
			reportPointerOnHeapRequired();
			mPointerOnHeapInitFunctionRequired = true;
			return true;
		}

		public boolean isPointerOnHeapRequired() {
			checkIsFrozen();
			return mPointerOnHeapRequired;
		}

		public boolean isPointerUncheckedWriteRequired() {
			checkIsFrozen();
			return mPointerUncheckedWriteRequired;
		}

		public boolean isPointerInitRequired() {
			checkIsFrozen();
			return mPointerInitWriteRequired;
		}

		public Set<CPrimitives> getDataOnHeapRequired() {
			checkIsFrozen();
			return mDataOnHeapRequired;
		}

		public boolean isPointerOnHeapInitFunctionRequired() {
			checkIsFrozen();
			return mPointerOnHeapInitFunctionRequired;
		}

		public boolean isDataOnHeapInitFunctionRequired(final CPrimitives prim) {
			checkIsFrozen();
			return mDataOnHeapInitFunctionRequired.contains(prim);
		}


		public Set<CPrimitives> getUncheckedWriteRequired() {
			checkIsFrozen();
			return mDataUncheckedWriteRequired;
		}

		public Set<CPrimitives> getInitWriteRequired() {
			checkIsFrozen();
			return mDataInitWriteRequired;
		}


		public boolean isMemoryModelInfrastructureRequired() {
			mMemoryModelInfrastructureRequiredHasBeenQueried = true;
			return mMemoryModelInfrastructureRequired;
		}

		/**
		 *
		 * @param mmdecl
		 * @return true if a change was made
		 */
		public boolean require(final MemoryModelDeclarations mmdecl) {
			if (mRequiredMemoryModelDeclarations.contains(mmdecl)) {
				// mmdecl has already been added -- nothing to do
				return false;
			}
			checkNotFrozen();
			requireMemoryModelInfrastructure();
			return mRequiredMemoryModelDeclarations.add(mmdecl);
		}

		public Set<MemoryModelDeclarations> getRequiredMemoryModelDeclarations() {
			checkIsFrozen();
			return Collections.unmodifiableSet(mRequiredMemoryModelDeclarations);
		}

		/**
		 * <ul>
		 *  <li>
		 *  <li> make all members of this class unmodifiable from this point on
		 * </ul>
		 * @param settings
		 */
		public void finish(final TranslationSettings settings) {
			boolean changedSomething = true;
			while (changedSomething) {
				changedSomething = false;
				for (final MemoryModelDeclarations mmdecl : mRequiredMemoryModelDeclarations) {
					changedSomething |=	mmdecl.resolveDependencies(this, settings);
				}
			}
			mIsFrozen = true;
		}

		private void checkIsFrozen() {
			if (!mIsFrozen) {
				throw new AssertionError("attempt to query before this has been frozen -- results might be wrong");
			}
		}

		private void checkNotFrozen() {
			if (mIsFrozen) {
				throw new AssertionError("attempt to modify, although this has been frozen already, perhaps we need to "
						+ "update MemoryModelDeclarations.resolveDependencies(..)");
			}
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

		IdentifierExpression constructIdentiferExpression(final ILocation loc) {
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
