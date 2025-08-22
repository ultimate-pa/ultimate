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
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The interface defining the functions for the different addressing modes.
 */
public interface IMemoryAdressing {
	/**
	 * Constructs the required metadata for the selected addressing mode.
	 *
	 * @param requiredFeatures
	 *            The Features that are currently needed for the program to be verified.
	 * @return The metadata declarations.
	 */
	List<Declaration> constructMetaData(RequiredMemoryModelFeatures requiredFeatures);

	/**
	 * Returns a list of metadata declarations needed for the memory model infrastructure.
	 *
	 * @return The declarations.
	 */
	List<MemoryModelDeclarations> metaDataDeclarations();

	/**
	 * Constructs a list of expressions that are used in the specifications of malloc.
	 *
	 * @return The expressions.
	 */
	List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(ILocation tuLoc,
			MemoryArea memoryArea, RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Constructs a list of expressions that are used in the specifications of dealloc.
	 *
	 * @return The expressions.
	 */
	List<Pair<Expression, Set<VariableLHS>>> constructDeallocSpecificationExpressions(ILocation tuLoc,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Returns a list of statements that are part of Ultimate.Init.
	 *
	 * @return The statements.
	 */
	List<Statement> constructUltimateInitStatements(ILocation loc,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler, BigInteger fixedAddressCounter);

	/**
	 * Constructs the expressions used in the specifications for allocInit.
	 *
	 * @return The expressions.
	 */
	List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(ILocation tuLoc,
			RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Add or subtracts a pointer and an integer.
	 *
	 * @return The calculated pointer.
	 */
	Expression doPointerArithmetic(final int operator, final ILocation loc, final Expression ptrAddress,
			final RValue integer, final ICType valueType, final CPrimitive integerExpressionType);

	/**
	 * Returns the step size in which the base value of the initial allocations must be increased.
	 *
	 * @return The step size.
	 */
	BigInteger fixedAddressCounterCountingStep(final Expression size);

	/**
	 * Returns the address for a field in a struct.
	 *
	 * @return The address.
	 */
	Expression constructAddressForStructField(final ILocation loc, final Expression baseAddress,
			final Offset fieldOffset, final CPrimitive sizeT);

	/**
	 * Adds an integer to a pointer.
	 *
	 * @return The new pointer.
	 */
	Expression addIntegerConstantToPointer(final ILocation loc, final Expression ptrExpr,
			final BigInteger integerConstant);

	/**
	 * Constructs the specifications that the pointer base address is valid.
	 *
	 * @return The specifications.
	 */
	List<Specification> constructPointerValidityCheck(final ILocation loc, final String ptrName,
			final String procedureName, final CheckMode mode,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Constructs the pointer base validity check expression.
	 *
	 * @return The expression.
	 */
	Expression constructPointerValidityCheckExpr(final ILocation loc, final Expression ptr,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Constructs the pointer target fully allocated specifications.
	 *
	 * @return The specifications.
	 */
	List<Specification> constructPointerTargetFullyAllocatedCheck(final ILocation loc, final Expression size,
			final String ptrName, final String procedureName, final CheckMode mode,
			final Boolean isBitVectorTranslation, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Constructs the statements used for the check if a freed pointer was valid.
	 *
	 * @return The statements.
	 */
	List<Statement> getChecksForFreeCall(final ILocation loc, final RValue pointerToBeFreed,
			final boolean isPointerCheckRequired, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Converts a pointer to an int.
	 *
	 * @return The new int expression.
	 */
	ExpressionResult convertPointerToInt(final ILocation loc, final ExpressionResult rexp, final CPrimitive newType);

	/**
	 * Converts an int to a pointer.
	 *
	 * @return The new pointer expression.
	 */
	ExpressionResult convertIntToPointer(final ILocation loc, final ExpressionResult rexp, final CPointer newType);

	/**
	 * Creates a function pointer, with the given offset.
	 *
	 * @return The function pointer.
	 */
	Expression createFunctionPointer(final ILocation loc, final BigInteger offset);

	/**
	 * Adds an expression to a pointer.
	 *
	 * @return The new pointer.
	 */
	Expression addExpressionToPointer(final ILocation loc, final Expression ptrExpr, final Expression expr);

	/**
	 * Returns a pointer to the last character of a string.
	 *
	 * @return The pointer.
	 */
	Expression lastCharOfString(final ILocation loc, final CPrimitive sizeT, final IdentifierExpression len,
			final IdentifierExpression returnValue);

	/**
	 * Creates the assume statement used in the handling of strchr.
	 *
	 * @return The statement.
	 */
	AssumeStatement strChrAssumeStatement(final ILocation loc, final Expression tmpExpr, final Expression argSPtr,
			final Expression nullPtrExpr, final Expression lengthArray);

	/**
	 * Constructs assert / assume statements for ptr memsafety checks.
	 *
	 * @return The statements.
	 */
	List<Statement> constructMemSafeStatementsForPointerExpression(final ILocation loc, final Expression ptr,
			final CheckMode pointerBaseValid, final CheckMode pointerTargetFullyAllocated,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);

	/**
	 * Construct the assume to check that src and dest don't overlap.
	 *
	 * @return The assume statement.
	 */
	Statement checksForStringCopyOverlapping(final ILocation loc, final Expression src, final Expression srcId,
			final Expression destId, final Expression dest);

	/**
	 * Constructs the rhs for the assignment statement of an heap data array.
	 *
	 * @return The expression.
	 */
	Expression[] rhsAssignmentStatementHda(final ILocation loc, final HeapDataArray hda, final Expression baseAddress);

	/**
	 * Returns an initial pointer with the same base address. If 2D-Addressing, than the offset is 0.
	 *
	 * @return The initial pointer.
	 */
	Expression initialPointerFromPointer(final ILocation loc, final Expression ptr);

	/**
	 * Subtracts two pointers.
	 *
	 * @return An {@link Expression} that represents the difference of two Pointers.
	 */
	Expression doPointerSubtraction(final ILocation loc, final Expression ptr1, final Expression ptr2,
			final ICType pointsToType);

	/**
	 * Constructs the statements that are present in the body of the Boogie realloc implementation.
	 *
	 * @return The statements.
	 */
	List<Statement> constructReallocBodyStatements(final ILocation loc, final String procName,
			final Collection<HeapDataArray> heapDataArrays, final BoogieType pointerType,
			final IdentifierExpression ptrIdExprImpl, final VariableLHS resultLhsImpl,
			final IdentifierExpression resultExprImpl, final IdentifierExpression sizeIdExprImpl,
			final RequiredMemoryModelFeatures requiredFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler);
}
