package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
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

	private final IMemoryAdressing mMemoryAddressing;
	private final IMemoryStructure mMemoryStructure;

	public MemoryModel(final TranslationSettings settings, final TypeSizes typeSizes, final ITypeHandler typeHandler,
			final ExpressionTranslation exprTranslation, final IBooleanArrayHelper booleanArrayHelper,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer) {
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mExpressionTranslation = exprTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
		mTypeSizeAndOffsetComputer = typeSizeAndOffsetComputer;

		mMemoryAddressing = MemoryModelFactory.createMemoryAddressing(settings, mTypeHandler, mExpressionTranslation,
				mBooleanArrayHelper, mTypeSizes, mTypeSizeAndOffsetComputer);
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
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return mMemoryAddressing.constructUltimateInitStatements(loc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
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

}
