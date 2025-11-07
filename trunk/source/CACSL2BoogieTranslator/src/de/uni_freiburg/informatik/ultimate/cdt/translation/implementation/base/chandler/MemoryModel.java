package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.Collection;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.BaseMemoryStructure.ReadWriteDefinition;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * The memory model consisting of a MemoryAdressing and a MemoryStructure.
 */
public class MemoryModel {
	private final IMemoryAdressing mMemoryAddressing;
	private final IMemoryStructure mMemoryStructure;

	/**
	 * This enum represents the valid combinations of memory structure and memory adressing.
	 */
	private enum Combinations {
		ONE_Dimensional_SingleBitPrecise(MemoryAddressing1D.class, MemoryStructureSingleBitprecise.class),
		ONE_Dimensional_MultiBitPrecise(MemoryAddressing1D.class, MemoryStructureMultiBitprecise.class),
		ONE_Dimensional_Unbounded(MemoryAddressing1D.class, MemoryStructureUnbounded.class),
		TWO_Dimensional_MultiBitPrecise(MemoryAddressing2D.class, MemoryStructureMultiBitprecise.class),
		TWO_Dimensional_SingleBitPrecise(MemoryAddressing2D.class, MemoryStructureSingleBitprecise.class),
		TWO_Dimensional_Unbounded(MemoryAddressing2D.class, MemoryStructureUnbounded.class);

		private final Class<? extends IMemoryAdressing> mAddressingType;
		private final Class<? extends IMemoryStructure> mStructureType;

		Combinations(final Class<? extends IMemoryAdressing> addressingType,
				final Class<? extends IMemoryStructure> structureType) {
			mAddressingType = addressingType;
			mStructureType = structureType;
		}

		/**
		 * Checks if the given combination is a valid one.
		 *
		 * @return If it is valid.
		 */
		public static boolean isValid(final Class<? extends IMemoryAdressing> addressingType,
				final Class<? extends IMemoryStructure> structureType) {
			for (final var value : values()) {
				if (value.mAddressingType.equals(addressingType) && value.mStructureType.equals(structureType)) {
					return true;
				}
			}
			return false;
		}
	}

	/**
	 * The factory method that creates a memory model with a valid combination of addressing and structure.
	 *
	 * @return The memory model.
	 */
	public static MemoryModel create(final TranslationSettings settings, final ITypeHandler typeHandler,
			final ExpressionTranslation exprTranslation, final IBooleanArrayHelper booleanArrayHelper,
			final TypeSizes typeSizes, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final FunctionDeclarations functionDeclarations, final IMemoryPointer pointer) {
		final var addressing = createAddressing(settings, typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
				typeSizeAndOffsetComputer, functionDeclarations, pointer);
		final var structure = createStructure(settings, typeSizes, typeHandler);

		if (!Combinations.isValid(addressing.getClass(), structure.getClass())) {
			throw new UnsupportedOperationException("The combination of addressing: " + addressing.getClass()
					+ " and structure " + structure.getClass() + " is invalid!");
		}

		return new MemoryModel(addressing, structure);
	}

	/**
	 * The factory method for creating the concrete memory structure instance.
	 *
	 * @return A concrete instance of IMemoryAdressing.
	 */
	private static IMemoryAdressing createAddressing(final TranslationSettings settings, final ITypeHandler typeHandler,
			final ExpressionTranslation exprTranslation, final IBooleanArrayHelper booleanArrayHelper,
			final TypeSizes typeSizes, final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final FunctionDeclarations functionDeclarations, final IMemoryPointer pointer) {

		if (pointer instanceof final MemoryPointer1D p) {
			return new MemoryAddressing1D(typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
					typeSizeAndOffsetComputer, settings, functionDeclarations, p);
		} else if (pointer instanceof final MemoryPointer2D p) {
			return new MemoryAddressing2D(typeHandler, exprTranslation, booleanArrayHelper, typeSizes,
					typeSizeAndOffsetComputer, settings.getPointerIntegerCastMode(), functionDeclarations, p);
		}

		throw new UnsupportedOperationException("Unknown pointer instance: " + pointer.getClass());
	}

	/**
	 * The factory method for creating the concrete memory structure instance.
	 *
	 * @return A concrete instance of IMemoryStructure.
	 */
	private static IMemoryStructure createStructure(final TranslationSettings settings, final TypeSizes typeSizes,
			final ITypeHandler typeHandler) {
		final var memoryStructurePreference = settings.getMemoryStructurePreference();
		if (memoryStructurePreference.isBitVectorRepresentation() && !settings.isBitvectorTranslation()) {
			throw new UnsupportedOperationException("Memory Structure: " + memoryStructurePreference
					+ " is only available in using the bitprecise translation");
		}

		switch (memoryStructurePreference) {
		case HoenickeLindenmann_1ByteResolution:
		case HoenickeLindenmann_2ByteResolution:
		case HoenickeLindenmann_4ByteResolution:
		case HoenickeLindenmann_8ByteResolution:
			return new MemoryStructureSingleBitprecise(memoryStructurePreference.getByteSize(), typeSizes,
					typeHandler);
		case HoenickeLindenmann_Original:
			if (settings.isBitvectorTranslation()) {
				return new MemoryStructureMultiBitprecise(typeSizes, typeHandler);
			}
			return new MemoryStructureUnbounded(typeSizes, typeHandler);
		default:
			throw new UnsupportedOperationException(memoryStructurePreference + " is an invalid memory structure.");
		}
	}

	private MemoryModel(final IMemoryAdressing memoryAdressing, final IMemoryStructure memoryStructure) {
		mMemoryAddressing = memoryAdressing;
		mMemoryStructure = memoryStructure;
	}

	public int singleBitPreciseResolution() {
		assert mMemoryStructure instanceof MemoryStructureSingleBitprecise;
		return ((MemoryStructureSingleBitprecise) mMemoryStructure).getResolution();
	}

	public boolean isSingleBitPreciseStructure() {
		return mMemoryStructure instanceof MemoryStructureSingleBitprecise;
	}

	public String getReadProcedureName(final CPrimitives primitive) {
		return mMemoryStructure.getReadProcedureName(primitive);
	}

	public String getUncheckedReadProcedureName(final CPrimitives primitive) {
		return mMemoryStructure.getUncheckedReadProcedureName(primitive);
	}

	public String getWriteProcedureName(final CPrimitives primitive) {
		return mMemoryStructure.getWriteProcedureName(primitive);
	}

	public String getUncheckedWriteProcedureName(final CPrimitives primitive) {
		return mMemoryStructure.getUncheckedWriteProcedureName(primitive);
	}

	public String getInitWriteProcedureName(final CPrimitives primitive) {
		return mMemoryStructure.getInitWriteProcedureName(primitive);
	}

	public String getReadPointerProcedureName() {
		return mMemoryStructure.getReadPointerProcedureName();
	}

	public String getUncheckedReadPointerProcedureName() {
		return mMemoryStructure.getUncheckedReadPointerProcedureName();
	}

	public String getWritePointerProcedureName() {
		return mMemoryStructure.getWritePointerProcedureName();
	}

	public String getUncheckedWritePointerProcedureName() {
		return mMemoryStructure.getUncheckedWritePointerProcedureName();
	}

	public String getInitPointerProcedureName() {
		return mMemoryStructure.getInitPointerProcedureName();
	}

	public HeapDataArray getDataHeapArray(final CPrimitives primitive) {
		return mMemoryStructure.getDataHeapArray(primitive);
	}

	public HeapDataArray getPointerHeapArray() {
		return mMemoryStructure.getPointerHeapArray();
	}

	public Collection<HeapDataArray> getDataHeapArrays(final RequiredMemoryModelFeatures requiredFeatures) {
		return mMemoryStructure.getDataHeapArrays(requiredFeatures);
	}

	List<ReadWriteDefinition> getReadWriteDefinitionForHeapDataArray(final HeapDataArray hda,
			final RequiredMemoryModelFeatures requiredMemoryStructureFeatures) {
		return mMemoryStructure.getReadWriteDefinitionForHeapDataArray(hda, requiredMemoryStructureFeatures);
	}

	/**
	 * Constructs the metadata depending on the active memory addressing mode.
	 *
	 * @param requiredFeatures
	 *            The required features.
	 * @return The declarations.
	 */
	public List<Declaration> constructMetaData(final RequiredMemoryModelFeatures requiredFeatures) {
		return mMemoryAddressing.constructMetaData(requiredFeatures);
	}

	/**
	 * Returns the list of metadata declarations
	 *
	 * @return
	 */
	public List<MemoryModelDeclarations> metaDataDeclarations() {
		return mMemoryAddressing.getMetaDataDeclarations();
	}

	/**
	 * Constructs the expressions used in the specifications for malloc.
	 *
	 * @return A list of a pair consisting of an expression and a set of the global variables that must be added to the
	 *         modifies clause.
	 */
	public List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(final ILocation tuLoc,
			final MemoryArea memoryArea, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructMallocSpecificationExpressions(tuLoc, memoryArea, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	/**
	 * Constructs the expressions used in the specifications for dealloc.
	 *
	 * @return A list of a pair consisting of an expression and a set of the global variables that must be added to the
	 *         modifies clause.
	 */
	public List<Triple<Expression, Set<VariableLHS>, Boolean>> constructDeallocSpecificationExpressions(
			final ILocation tuLoc, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructDeallocSpecificationExpressions(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	/**
	 * Constructs the statements used in Ultimate.Init.
	 *
	 * @return The statements.
	 */
	List<Statement> constructUltimateInitStatements(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler, final BigInteger fixedAddressCounter) {
		return mMemoryAddressing.constructUltimateInitStatements(loc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler, fixedAddressCounter);
	}

	/**
	 * Constructs the expressions used in the specifications for allocInit.
	 *
	 * @return The expressions.
	 */
	public List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructAllocInitSpecificationExpressions(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	/**
	 * Add or subtracts a pointer and an integer.
	 *
	 * @return The calculated pointer.
	 */
	public Expression doPointerArithmetic(final int operator, final ILocation loc, final Expression ptrAddress,
			final RValue integer, final ICType valueType, final CPrimitive integerExpressionType) {
		return mMemoryAddressing.doPointerArithmetic(operator, loc, ptrAddress, integer, valueType,
				integerExpressionType);
	}

	/**
	 * Returns the step size in which the base value of the initial allocations must be increased.
	 *
	 * @return The step size.
	 */
	public BigInteger fixedAddressCounterCountingStep(final Expression size) {
		return mMemoryAddressing.getFixedAddressCounterCountingStep(size);
	}

	/**
	 * Returns the address for struct field.
	 *
	 * @return The address.
	 */
	public Expression constructAddressForStructField(final ILocation loc, final Expression baseAddress,
			final Offset fieldOffset, final CPrimitive sizeT) {
		if (fieldOffset.isBitfieldOffset()) {
			throw new UnsupportedOperationException("Bitfield read");
		}
		return mMemoryAddressing.constructAddressForStructField(loc, baseAddress, fieldOffset, sizeT);
	}

	/**
	 * Adds an integer to a pointer.
	 *
	 * @return The new pointer.
	 */
	public Expression addIntegerConstantToPointer(final ILocation loc, final Expression ptrExpr,
			final BigInteger integerConstant) {
		return mMemoryAddressing.addIntegerConstantToPointer(loc, ptrExpr, integerConstant);
	}

	/**
	 * Constructs the specifications that the pointer base address is valid.
	 *
	 * @return The specifications.
	 */
	public List<Specification> constructPointerBaseValidityCheck(final ILocation loc, final String ptrName,
			final String procedureName, final CheckMode mode,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructPointerValidityCheck(loc, ptrName, procedureName, mode,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

	/**
	 * Constructs the pointer base validity check expression.
	 *
	 * @return The expression.
	 */
	Expression constructPointerBaseValidityCheckExpr(final ILocation loc, final Expression ptr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructPointerValidityCheckExpr(loc, ptr, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	/**
	 * Constructs the pointer target fully allocated specifications.
	 *
	 * @return The specifications.
	 */
	public List<Specification> constructPointerTargetFullyAllocatedCheck(final ILocation loc, final Expression size,
			final String ptrName, final String procedureName, final CheckMode mode,
			final Boolean isBitVectorTranslation, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructPointerTargetFullyAllocatedCheck(loc, size, ptrName, procedureName, mode,
				isBitVectorTranslation, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

	/**
	 * Constructs the statements used for the check if a freed pointer was valid.
	 *
	 * @return The statements.
	 */
	List<Statement> getChecksForFreeCall(final ILocation loc, final RValue pointerToBeFreed,
			final boolean isPointerCheckRequired, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.getChecksForFreeCall(loc, pointerToBeFreed, isPointerCheckRequired,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

	/**
	 * Converts a pointer to an int.
	 *
	 * @return The new int expression.
	 */
	public final ExpressionResult convertPointerToInt(final ILocation loc, final ExpressionResult rexp,
			final CPrimitive newType) {
		return mMemoryAddressing.convertPointerToInt(loc, rexp, newType);
	}

	/**
	 * Converts an int to a pointer.
	 *
	 * @return The new pointer expression.
	 */
	public final ExpressionResult convertIntToPointer(final ILocation loc, final ExpressionResult rexp,
			final CPointer newType) {
		return mMemoryAddressing.convertIntToPointer(loc, rexp, newType);
	}

	/**
	 * Creates a function pointer, with the given offset.
	 *
	 * @return The function pointer.
	 */
	public final Expression createFunctionPointer(final ILocation loc, final BigInteger offset) {
		return mMemoryAddressing.constructFunctionPointer(loc, offset);
	}

	/**
	 * Adds an expression to a pointer.
	 *
	 * @return The new pointer.
	 */
	public Expression addExpressionToPointer(final ILocation loc, final Expression ptrExpr, final Expression expr) {
		return mMemoryAddressing.addExpressionToPointer(loc, ptrExpr, expr);
	}

	/**
	 * Returns a pointer to the last character of a string.
	 *
	 * @return The pointer.
	 */
	public Expression lastCharOfString(final ILocation loc, final CPrimitive sizeT, final IdentifierExpression len,
			final IdentifierExpression returnValue) {
		return mMemoryAddressing.getLastCharOfString(loc, sizeT, len, returnValue);
	}

	/**
	 * Returns a pointer with the same base address but an offset of 0.
	 *
	 * @return A pointer with offset 0.
	 */
	public Expression initialPointerFromPointer(final ILocation loc, final Expression ptr) {
		return mMemoryAddressing.constructInitialPointerFromPointer(loc, ptr);
	}

	/**
	 * Creates the assume statement used in the handling of strchr.
	 *
	 * @return The statement.
	 */
	public final AssumeStatement strChrAssumeStatement(final ILocation loc, final Expression tmpExpr,
			final Expression argSPtr, final Expression nullPtrExpr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructStrChrAssumeStatement(loc, tmpExpr, argSPtr, nullPtrExpr, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}

	/**
	 * Constructs assert / assume statements for ptr memsafety checks.
	 *
	 * @return The statements.
	 */
	public List<Statement> constructMemSafeStatementsForPointerExpression(final ILocation loc, final Expression ptr,
			final CheckMode pointerBaseValid, final CheckMode pointerTargetFullyAllocated,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructMemSafeStatementsForPointerExpression(loc, ptr, pointerBaseValid,
				pointerTargetFullyAllocated, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

	/**
	 * Construct the assume to check that src and dest don't overlap.
	 *
	 * @return The assume statement.
	 */
	public Statement checksForStringCopyOverlapping(final ILocation loc, final Expression src, final Expression srcId,
			final Expression destId, final Expression dest) {
		return mMemoryAddressing.checksForStringCopyOverlapping(loc, src, srcId, destId, dest);
	}

	/**
	 * Constructs the rhs for the assignment statement of an heap data array.
	 *
	 * @return The expression.
	 */
	public Expression[] rhsAssignmentStatementHda(final ILocation loc, final HeapDataArray hda,
			final Expression baseAddress) {
		return mMemoryAddressing.constructRhsAssignmentStatementHda(loc, hda, baseAddress);
	}

	/**
	 * Constructs an expression representing a pointer subtraction.
	 *
	 * @return The expression.
	 */
	public Expression doPointerSubtraction(final ILocation loc, final Expression ptr1, final Expression ptr2,
			final ICType pointsToType) {
		return mMemoryAddressing.doPointerSubtraction(loc, ptr1, ptr2, pointsToType);
	}

	/**
	 * Constructs the statements that are present in the body of the Boogie realloc implementation.
	 *
	 * @return The statements.
	 */
	public List<Statement> constructReallocBodyStatements(final ILocation loc, final String procName,
			final Collection<HeapDataArray> heapDataArrays, final BoogieType pointerType,
			final IdentifierExpression ptrIdExprImpl, final VariableLHS resultLhsImpl,
			final IdentifierExpression resultExprImpl, final IdentifierExpression sizeIdExprImpl,
			final RequiredMemoryModelFeatures requiredFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructReallocBodyStatements(loc, procName, heapDataArrays, pointerType,
				ptrIdExprImpl, resultLhsImpl, resultExprImpl, sizeIdExprImpl, requiredFeatures,
				memoryModelDeclarationsHandler);
	}

	public Expression getValidArray(final ILocation loc, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.getValidArray(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

}
