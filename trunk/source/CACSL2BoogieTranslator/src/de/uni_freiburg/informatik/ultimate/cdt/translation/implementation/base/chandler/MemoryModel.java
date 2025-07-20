package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The memory model consisting of a MemoryAdressing and a MemoryStructure.
 */
public class MemoryModel {
	private final TypeSizes mTypeSizes;
	private final ITypeHandler mTypeHandler;
	private final IBooleanArrayHelper mBooleanArrayHelper;
	private final ExpressionTranslation mExpressionTranslation;
	private final TypeSizeAndOffsetComputer mTypeSizeAndOffsetComputer;
	private final FunctionDeclarations mFunctionDeclarations;

	private final IMemoryAdressing mMemoryAddressing;
	private final IMemoryStructure mMemoryStructure;

	public MemoryModel(final TranslationSettings settings, final TypeSizes typeSizes, final ITypeHandler typeHandler,
			final ExpressionTranslation exprTranslation, final IBooleanArrayHelper booleanArrayHelper,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final FunctionDeclarations functionDeclarations) {
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mExpressionTranslation = exprTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;
		mFunctionDeclarations = functionDeclarations;

		mMemoryAddressing = MemoryModelFactory.createMemoryAddressing(settings, mTypeHandler, mExpressionTranslation,
				mBooleanArrayHelper, mTypeSizes, mTypeSizeAndOffsetComputer, mFunctionDeclarations);
		mMemoryStructure = MemoryModelFactory.createMemoryStructure(settings, mTypeSizes, mTypeHandler);
	}

	public IMemoryStructure memoryStructure() {
		return mMemoryStructure;
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
		return mMemoryAddressing.metaDataDeclarations();
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
	public List<Pair<Expression, Set<VariableLHS>>> constructDeallocSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
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
			final RValue integer, final ICType valueType) {
		return mMemoryAddressing.doPointerArithmetic(operator, loc, ptrAddress, integer, valueType);
	}

	/**
	 * Returns the step size in which the base value of the initial allocations must be increased.
	 *
	 * @return The step size.
	 */
	public BigInteger fixedAddressCounterCountingStep(final Expression size) {
		return mMemoryAddressing.fixedAddressCounterCountingStep(size);
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
		return mMemoryAddressing.constructPointerBaseValidityCheck(loc, ptrName, procedureName, mode,
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
		return mMemoryAddressing.constructPointerBaseValidityCheckExpr(loc, ptr, requiredMemoryModelFeatures,
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
		return mMemoryAddressing.createFunctionPointer(loc, offset);
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
		return mMemoryAddressing.lastCharOfString(loc, sizeT, len, returnValue);
	}

	/**
	 * Returns a pointer with the same base address but an offset of 0.
	 *
	 * @return A pointer with offset 0.
	 */
	public Expression initialPointerFromPointer(final ILocation loc, final Expression ptr) {
		final Expression zero = mExpressionTranslation.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);

		return MemoryHandler.constructPointerFromBaseAndOffset(MemoryHandler.getPointerBaseAddress(ptr, loc), zero,
				loc);
	}
}
