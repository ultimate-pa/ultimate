package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.NonBijectiveMappingOneDimensional;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.OverapproximationUF2OneDimensional;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;

/**
 * The one dimensional memory addressing.
 */
public class OneDimensionalMemoryAddressing extends BaseMemoryAdressing<OneDimensionalPointer> {
	public OneDimensionalMemoryAddressing(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final PointerIntegerConversion pointerIntegerMode, final FunctionDeclarations functionDeclarations,
			final OneDimensionalPointer pointer) {
		super(typeHandler, exprTranslation, booleanArrayHelper, typeSizes, typeSizeAndOffsetComputer, pointer);

		mPointerIntegerConversion = switch (pointerIntegerMode) {
		case NonBijectiveMapping:
			yield new NonBijectiveMappingOneDimensional(exprTranslation, pointer);
		case Overapproximate:
			yield new OverapproximationUF2OneDimensional(exprTranslation, functionDeclarations, typeHandler, pointer);
		default:
			throw new UnsupportedOperationException(
					"Pointer-Integer conversion not yet implemented " + pointerIntegerMode);
		};

		mMemoryManagementStrategy = new SimpleIncreasingStrategy<>(typeSizes, exprTranslation, typeHandler,
				typeSizeAndOffsetComputer, this);
	}

	@Override
	public List<Declaration> constructMetaData(final RequiredMemoryModelFeatures requiredFeatures) {
		final var metaDataDeclarations = new ArrayList<Declaration>();

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_INITIAL_ALLOCATIONS)) {
			metaDataDeclarations.add(constructInitialAllocationsConstant());
		}

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_STACK_ALLOCATIONS)) {
			metaDataDeclarations.add(constructStackAllocationsVariable());
		}

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_HEAP_ALLOCATIONS)) {
			metaDataDeclarations.add(constructHeapAllocationsVariable());
		}

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER)) {
			metaDataDeclarations.add(constructStackHeapBarrierConstant());
		}

		return metaDataDeclarations;
	}

	/**
	 * Constructs the declaration of the constant that holds the count of all initial allocations.
	 *
	 * @return The declaration.
	 */
	private VariableDeclaration constructInitialAllocationsConstant() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_INITIAL_ALLOCATIONS.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	/**
	 * Constructs the declaration of the variable holding the count of stack allocations.
	 *
	 * @return The declaration.
	 */
	private VariableDeclaration constructStackAllocationsVariable() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_STACK_ALLOCATIONS.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	/**
	 * Constructs the declaration of the variable holding the count of heap allocations.
	 *
	 * @return The declaration.
	 */
	private VariableDeclaration constructHeapAllocationsVariable() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_HEAP_ALLOCATIONS.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	@Override
	public List<MemoryModelDeclarations> metaDataDeclarations() {
		return List.of(MemoryModelDeclarations.ULTIMATE_INITIAL_ALLOCATIONS,
				MemoryModelDeclarations.ULTIMATE_STACK_ALLOCATIONS, MemoryModelDeclarations.ULTIMATE_HEAP_ALLOCATIONS);
	}

	@Override
	public Expression doPointerArithmetic(final int operator, final ILocation loc, final Expression ptrAddress,
			final RValue integer, final ICType valueType) {

		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		if (mTypeSizes.getSize(((CPrimitive) integer.getCType().getUnderlyingType()).getType()) != mTypeSizes
				.getSize(cTypeOfPointerComponent.getType())) {
			throw new UnsupportedOperationException("not yet implemented, conversion is needed");
		}

		final Expression pointerBase = mMemoryPointer.pointerAddress(ptrAddress, loc);
		final Expression timesSizeOf =
				multiplyWithSizeOfAnotherType(loc, valueType, integer.getValue(), cTypeOfPointerComponent);

		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, operator, pointerBase,
				cTypeOfPointerComponent, timesSizeOf, cTypeOfPointerComponent);

		return mMemoryPointer.createPointerFromBase(sum, loc);
	}

	@Override
	public BigInteger fixedAddressCounterCountingStep(final Expression size) {
		return mTypeSizes.extractIntegerValue(size, new CPrimitive(CPrimitives.LONG));
	}

	@Override
	public Expression constructAddressForStructField(final ILocation loc, final Expression baseAddress,
			final Offset fieldOffset, final CPrimitive sizeT) {

		final Expression pointerBase = mMemoryPointer.pointerAddress(baseAddress, loc);
		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				pointerBase, sizeT, fieldOffset.getAddressOffsetAsExpression(loc), sizeT);

		return mMemoryPointer.createPointerFromBase(sum, loc);
	}

	@Override
	public Expression addIntegerConstantToPointer(final ILocation loc, final Expression ptrExpr,
			final BigInteger integerConstant) {
		final Expression integerExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), integerConstant);

		return addExpressionToPointer(loc, ptrExpr, integerExpr);
	}

	@Override
	public Expression createFunctionPointer(final ILocation loc, final BigInteger offset) {
		final Expression base = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), functionPointerPointerBaseValue);

		final Expression integerExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), offset);

		final Expression baseMinus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_minus, base,
						mTypeSizeAndOffsetComputer.getSizeT(), integerExpr, mTypeSizeAndOffsetComputer.getSizeT());

		return mMemoryPointer.createPointerFromBase(baseMinus, loc);
	}

	@Override
	public Expression addExpressionToPointer(final ILocation loc, final Expression ptrExpr, final Expression expr) {
		final Expression base = mMemoryPointer.pointerAddress(ptrExpr, loc);

		final Expression basePlus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, base,
						mTypeSizeAndOffsetComputer.getSizeT(), expr, mTypeSizeAndOffsetComputer.getSizeT());

		return mMemoryPointer.createPointerFromBase(basePlus, loc);
	}

	@Override
	public Expression lastCharOfString(final ILocation loc, final CPrimitive sizeT, final IdentifierExpression len,
			final IdentifierExpression returnValue) {
		final var lenMinusOne = mExpressionTranslation.constructArithmeticIntegerExpression(loc,
				IASTBinaryExpression.op_minus, mExpressionTranslation.applyWraparound(loc, sizeT, len), sizeT,
				mTypeSizes.constructLiteralForIntegerType(loc, sizeT, BigInteger.ONE), sizeT);

		return mMemoryPointer.createPointerFromBase(lenMinusOne, loc);
	}

	@Override
	public AssumeStatement strChrAssumeStatement(final ILocation loc, final Expression tmpExpr,
			final Expression argSPtr, final Expression nullPtrExpr, final Expression lengthArray) {
		// TODO check if this is valid, we cannot check for in range in the one dimensional model
		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final var baseEqualNull = baseEqualsNull(loc, tmpExpr, cTypeOfPointerComponent, nullPtrExpr);
		final var baseEqual = baseEqual(loc, tmpExpr, cTypeOfPointerComponent, argSPtr);

		return new AssumeStatement(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, baseEqualNull, baseEqual));
	}

	@Override
	public Expression initialPointerFromPointer(final ILocation loc, final Expression ptr) {
		return mMemoryPointer.createPointerFromBase(mMemoryPointer.pointerAddress(ptr, loc), loc);
	}

	@Override
	public Expression doPointerSubtraction(final ILocation loc, final Expression ptr1, final Expression ptr2,
			final ICType pointsToType) {
		final Expression ptr1Base = mMemoryPointer.pointerAddress(ptr1, loc);
		final Expression ptr2Base = mMemoryPointer.pointerAddress(ptr2, loc);

		return pointerComponentSubtraction(loc, ptr1Base, ptr2Base, pointsToType);
	}

	@Override
	public List<Statement> constructReallocBodyStatements(final ILocation loc, final String procName,
			final Collection<HeapDataArray> heapDataArrays, final BoogieType pointerType,
			final IdentifierExpression ptrIdExprImpl) {
		// TODO: Implementation for realloc
		throw new UnsupportedOperationException("Realloc is currently not supported in the 1D memory addressing!");
	}
}
