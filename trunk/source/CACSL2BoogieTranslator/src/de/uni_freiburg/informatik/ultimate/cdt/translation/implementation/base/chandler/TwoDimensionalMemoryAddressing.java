package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizeAndOffsetComputer.Offset;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.NonBijectiveMapping;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.OverapproximationUF;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.ICType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Spec;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.PointerIntegerConversion;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The two dimensional memory addressing.
 */
public class TwoDimensionalMemoryAddressing extends BaseMemoryAdressing {

	public TwoDimensionalMemoryAddressing(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes,
			final TypeSizeAndOffsetComputer typeSizeAndOffsetComputer,
			final PointerIntegerConversion pointerIntegerMode, final FunctionDeclarations functionDeclarations) {
		super(typeHandler, exprTranslation, booleanArrayHelper, typeSizes, typeSizeAndOffsetComputer);

		mPointerIntegerConversion = switch (pointerIntegerMode) {
		case NonBijectiveMapping:
			yield new NonBijectiveMapping(exprTranslation, typeSizes);
		case Overapproximate:
			yield new OverapproximationUF(exprTranslation, functionDeclarations, typeHandler, typeSizes);
		default:
			throw new UnsupportedOperationException(
					"Pointer-Integer conversion not yet implemented " + pointerIntegerMode);
		};
	}

	@Override
	public List<Declaration> constructMetaData(final RequiredMemoryModelFeatures requiredFeatures) {
		final var metaDataDeclarations = new ArrayList<Declaration>();
		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_LENGTH)) {
			metaDataDeclarations.add(constructLengthArrayDeclaration());
		}

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_VALID)) {
			metaDataDeclarations.add(constructValidArrayDeclaration());
		}

		if (requiredFeatures.getRequiredMemoryStructureDeclarations()
				.contains(MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER)) {
			metaDataDeclarations.add(constructStackHeapBarrierConstant());
		}

		return metaDataDeclarations;
	}

	/**
	 * Constructs the declaration of the length array, tracking the length of each memory block.
	 *
	 * @return The declaration.
	 */
	private VariableDeclaration constructLengthArrayDeclaration() {
		// var #length : [int]int;
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final ASTType pointerComponentType =
				mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents());
		final BoogieType boogieType =
				BoogieType.createArrayType(0, new BoogieType[] { (BoogieType) pointerComponentType.getBoogieType() },
						(BoogieType) pointerComponentType.getBoogieType());
		final ASTType lengthType = new ArrayType(ignoreLoc, boogieType, new String[0],
				new ASTType[] { pointerComponentType }, pointerComponentType);
		final VarList vlL =
				new VarList(ignoreLoc, new String[] { MemoryModelDeclarations.ULTIMATE_LENGTH.getName() }, lengthType);
		return new VariableDeclaration(ignoreLoc, new Attribute[0], new VarList[] { vlL });
	}

	/**
	 * Constructs the declaration of the valid array, tracking if a memory block is allocated.
	 *
	 * @return The declaration.
	 */
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

	@Override
	public List<MemoryModelDeclarations> metaDataDeclarations() {
		return List.of(MemoryModelDeclarations.ULTIMATE_VALID, MemoryModelDeclarations.ULTIMATE_LENGTH);
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructMallocSpecificationExpressions(final ILocation tuLoc,
			final MemoryArea memoryArea, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		final var memoryAreaName = memoryArea.getMemoryStructureDeclaration().getName();
		final var falseExpr = mBooleanArrayHelper.constructFalse();
		final var trueExpr = mBooleanArrayHelper.constructTrue();

		final var validArrayExpr = MemoryModelExpressionHelper.getValidArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final var stackHeapBarrierExpr = MemoryModelExpressionHelper.getStackHeapBarrier(tuLoc,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
		final var lengthArrayExpr = MemoryModelExpressionHelper.getLengthArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

		final var zeroNumericValueExpr = mTypeSizes.constructLiteralForIntegerType(tuLoc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final var resultExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.RES,
						new DeclarationInformation(StorageClass.PROC_FUNC_OUTPARAM, memoryAreaName));

		final var sizeExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(), SFO.SIZE,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, memoryAreaName));

		final var resBaseExpr = ExpressionFactory.constructStructAccessExpression(tuLoc, resultExpr, SFO.POINTER_BASE);

		final ArrayList<Pair<Expression, Set<VariableLHS>>> expressions = new ArrayList<>();

		// old(#valid)[#res!base] == false
		final var freshLocationCurrentlyNotValidExpr = ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ,
				ExpressionFactory.constructNestedArrayAccessExpression(tuLoc,
						ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, validArrayExpr),
						new Expression[] { resBaseExpr }),
				falseExpr);

		expressions.add(new Pair<>(freshLocationCurrentlyNotValidExpr, Collections.emptySet()));

		// #valid == old(#valid)[#res!base := true]
		final var validUpdateExpr =
				MemoryModelExpressionHelper.ensuresArrayUpdate(tuLoc, trueExpr, resBaseExpr, validArrayExpr);
		expressions.add(new Pair<>(validUpdateExpr,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(validArrayExpr))));

		// #res!offset == 0
		final var offsetEqualZeroExpr = offsetEqualsZeroExpr(tuLoc, resultExpr, zeroNumericValueExpr);
		expressions.add(new Pair<>(offsetEqualZeroExpr, Collections.emptySet()));

		// #res!base != 0
		final var baseNotEqualZeroExpr = baseNotEqualZeroExpr(tuLoc, resultExpr, zeroNumericValueExpr);
		expressions.add(new Pair<>(baseNotEqualZeroExpr, Collections.emptySet()));

		if (memoryArea == MemoryArea.STACK) {
			// #StackHeapBarrier < res!base
			final var baseGreaterThanBarrierExpr = baseGreaterThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(new Pair<>(baseGreaterThanBarrierExpr, Collections.emptySet()));
		} else if (memoryArea == MemoryArea.HEAP) {
			// res!base < #StackHeapBarrier
			final var baseSmallerThanBarrierExpr = baseSmallerThanBarrier(tuLoc, stackHeapBarrierExpr, resultExpr);
			expressions.add(new Pair<>(baseSmallerThanBarrierExpr, Collections.emptySet()));
		}

		// #length == old(#length)[#res!base := ~size]
		final var lengthUpdateExpr =
				ExpressionFactory
						.newBinaryExpression(tuLoc, Operator.COMPEQ, lengthArrayExpr,
								ExpressionFactory.constructArrayStoreExpression(
										tuLoc, ExpressionFactory.constructUnaryExpression(tuLoc,
												UnaryExpression.Operator.OLD, lengthArrayExpr),
										new Expression[] { resBaseExpr }, sizeExpr));
		expressions.add(new Pair<>(lengthUpdateExpr,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(lengthArrayExpr))));

		return expressions;
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructDeallocSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final var falseExpr = mBooleanArrayHelper.constructFalse();
		final var validArrayExpr = MemoryModelExpressionHelper.getValidArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

		final Expression addrExpr =
				ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogiePointerType(), SFO.ADDR,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM,
								MemoryModelDeclarations.ULTIMATE_DEALLOC.getName()));
		final Expression addrBaseExpr =
				ExpressionFactory.constructStructAccessExpression(tuLoc, addrExpr, SFO.POINTER_BASE);

		// #valid == old(#valid)[~addr!base := 0]
		final ArrayStoreExpression arrayStoreExpr = ExpressionFactory.constructArrayStoreExpression(tuLoc,
				ExpressionFactory.constructUnaryExpression(tuLoc, UnaryExpression.Operator.OLD, validArrayExpr),
				new Expression[] { addrBaseExpr }, falseExpr);

		final Expression updateValidArrayExpr =
				ExpressionFactory.newBinaryExpression(tuLoc, Operator.COMPEQ, validArrayExpr, arrayStoreExpr);

		return Collections.singletonList(new Pair<>(updateValidArrayExpr,
				Collections.singleton((VariableLHS) CTranslationUtil.convertExpressionToLHS(validArrayExpr))));
	}

	@Override
	public List<Statement> constructUltimateInitStatements(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler, final BigInteger fixedAddressCounter) {
		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final List<Statement> statements = new ArrayList<>();
		// TODO 20211115 Matthias: added the following assume-base initialization for
		// #valid[0] == 0. I presume that the assignment-case initialization is not
		// needed in any approach and can be dropped.
		if (true) {
			// assume #valid[0] == 0 (i.e., the memory at the NULL-pointer is
			// not allocated)
			final Expression zero =
					mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);
			final Expression literalThatRepresentsFalse = mBooleanArrayHelper.constructFalse();
			final Expression eq = ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ,
					ExpressionFactory.constructNestedArrayAccessExpression(loc,
							MemoryModelExpressionHelper.getValidArray(loc, requiredMemoryModelFeatures,
									memoryModelDeclarationsHandler),
							new Expression[] { zero }),
					literalThatRepresentsFalse);
			final AssumeStatement assume = new AssumeStatement(loc, eq);
			statements.add(assume);
		} else {
			// set #valid[0] = 0 (i.e., the memory at the NULL-pointer is
			// not allocated)
			final Expression zero =
					mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);
			final Expression literalThatRepresentsFalse = mBooleanArrayHelper.constructFalse();
			final AssignmentStatement assignment = MemoryHandler.constructOneDimensionalArrayUpdate(loc, zero,
					MemoryModelExpressionHelper.getValidArrayLhs(loc, requiredMemoryModelFeatures,
							memoryModelDeclarationsHandler),
					literalThatRepresentsFalse);

			statements.add(assignment);
		}

		// Add assume(0 < #StackHeapBarrier) to ensure that the null
		// pointer is on the heap.
		final Expression zero =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);
		final Expression zeroSmallerStackHeapBarrier =
				mExpressionTranslation
						.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_lessThan, zero,
								cTypeOfPointerComponent, MemoryModelExpressionHelper.getStackHeapBarrier(loc,
										requiredMemoryModelFeatures, memoryModelDeclarationsHandler),
								cTypeOfPointerComponent);

		statements.add(new AssumeStatement(loc, zeroSmallerStackHeapBarrier));

		return statements;
	}

	@Override
	public List<Pair<Expression, Set<VariableLHS>>> constructAllocInitSpecificationExpressions(final ILocation tuLoc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final var pointerBaseIdentifier = "ptrBase";
		final var procedureIdentifier = MemoryModelDeclarations.ULTIMATE_ALLOC_INIT.getName();

		final var trueExpr = mBooleanArrayHelper.constructTrue();
		final var validArrayExpr = MemoryModelExpressionHelper.getValidArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final var lengthArrayExpr = MemoryModelExpressionHelper.getLengthArray(tuLoc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final var size = ExpressionFactory.constructIdentifierExpression(tuLoc, mTypeHandler.getBoogieTypeForSizeT(),
				SFO.SIZE, new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureIdentifier));

		final var ptrBase = ExpressionFactory.constructIdentifierExpression(tuLoc,
				mTypeHandler.getBoogieTypeForPointerComponents(), pointerBaseIdentifier,
				new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureIdentifier));

		final ArrayList<Pair<Expression, Set<VariableLHS>>> expressions = new ArrayList<>();
		// ensures #valid[ptrBase] == true;
		final var validPtrBaseExpr =
				MemoryModelExpressionHelper.ensuresArrayHasValue(tuLoc, trueExpr, ptrBase, validArrayExpr);
		expressions.add(new Pair<>(validPtrBaseExpr, Collections.emptySet()));

		// ensures #length[ptrBase] == size;
		final var lengthPtrBaseSize =
				MemoryModelExpressionHelper.ensuresArrayHasValue(tuLoc, size, ptrBase, lengthArrayExpr);
		expressions.add(new Pair<>(lengthPtrBaseSize, Collections.emptySet()));

		return expressions;
	}

	@Override
	public Expression doPointerArithmetic(final int operator, final ILocation loc, final Expression ptrAddress,
			final RValue integer, final ICType valueType) {
		final var pointerComponentType = mExpressionTranslation.getCTypeOfPointerComponents();

		if (mTypeSizes.getSize(((CPrimitive) integer.getCType().getUnderlyingType()).getType()) != mTypeSizes
				.getSize(pointerComponentType.getType())) {
			throw new UnsupportedOperationException("not yet implemented, conversion is needed");
		}

		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(ptrAddress, loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(ptrAddress, loc);

		final Expression timesSizeOf =
				multiplyWithSizeOfAnotherType(loc, valueType, integer.getValue(), pointerComponentType);

		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, operator, pointerOffset,
				pointerComponentType, timesSizeOf, pointerComponentType);

		return MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
	}

	@Override
	public BigInteger fixedAddressCounterCountingStep(final Expression size) {
		return BigInteger.ONE;
	}

	@Override
	public Expression constructAddressForStructField(final ILocation loc, final Expression baseAddress,
			final Offset fieldOffset, final CPrimitive sizeT) {

		final Expression pointerBase = MemoryHandler.getPointerBaseAddress(baseAddress, loc);
		final Expression pointerOffset = MemoryHandler.getPointerOffset(baseAddress, loc);

		final Expression sum = mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus,
				pointerOffset, sizeT, fieldOffset.getAddressOffsetAsExpression(loc), sizeT);

		return MemoryHandler.constructPointerFromBaseAndOffset(pointerBase, sum, loc);
	}

	@Override
	public Expression addIntegerConstantToPointer(final ILocation loc, final Expression ptrExpr,
			final BigInteger integerConstant) {

		final Expression integerExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), integerConstant);

		return addExpressionToPointer(loc, ptrExpr, integerExpr);
	}

	@Override
	public List<Specification> constructPointerBaseValidityCheck(final ILocation loc, final String ptrName,
			final String procedureName, final CheckMode mode,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		if (mode == CheckMode.IGNORE) {
			return Collections.emptyList();
		}

		final Expression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));
		final Expression isValid = constructPointerBaseValidityCheckExpr(loc, ptrExpr, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);

		final boolean isFreeRequires = mode == CheckMode.CHECK ? false : true;

		final RequiresSpecification spec = new RequiresSpecification(loc, isFreeRequires, isValid);
		final Check check = new Check(Spec.MEMORY_DEREFERENCE);
		check.annotate(spec);
		return Collections.singletonList(spec);
	}

	@Override
	public List<Specification> constructPointerTargetFullyAllocatedCheck(final ILocation loc, final Expression size,
			final String ptrName, final String procedureName, final CheckMode mode,
			final Boolean isBitVectorTranslation, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {

		if (mode == CheckMode.IGNORE) {
			return Collections.emptyList();
		}

		final Expression ptrExpr =
				ExpressionFactory.constructIdentifierExpression(loc, mTypeHandler.getBoogiePointerType(), ptrName,
						new DeclarationInformation(StorageClass.PROC_FUNC_INPARAM, procedureName));

		final Expression ptrBase = MemoryHandler.getPointerBaseAddress(ptrExpr, loc);
		final Expression ptrOffset = MemoryHandler.getPointerOffset(ptrExpr, loc);
		final CPrimitive cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		//
		final Expression lengthArray = MemoryModelExpressionHelper.getLengthArray(loc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final Expression aae =
				ExpressionFactory.constructNestedArrayAccessExpression(loc, lengthArray, new Expression[] { ptrBase });
		final Expression sum =
				constructPointerBinaryArithmeticExpression(loc, IASTBinaryExpression.op_plus, size, ptrOffset);
		Expression leq = constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, sum, aae);

		//
		final Expression zeroNumericLiteral =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);

		final Expression offsetGeqZero = constructPointerBinaryComparisonExpression(loc,
				IASTBinaryExpression.op_lessEqual, zeroNumericLiteral, ptrOffset);

		if (isBitVectorTranslation) {
			/*
			 * Check that "#ptr!offset <= #ptr!offset + #sizeOf[Written|Read]Type", i.e., the sum does not overflow.
			 * (This works because #size.. is positive.)
			 */

			final Expression noOverFlowInSum =
					constructPointerBinaryComparisonExpression(loc, IASTBinaryExpression.op_lessEqual, ptrOffset, sum);
			leq = ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leq, noOverFlowInSum);
		}

		final Expression offsetInAllocatedRange =
				ExpressionFactory.newBinaryExpression(loc, BinaryExpression.Operator.LOGICAND, leq, offsetGeqZero);

		final boolean isFreeRequires = mode == CheckMode.CHECK ? false : true;
		final RequiresSpecification spec = new RequiresSpecification(loc, isFreeRequires, offsetInAllocatedRange);
		final Check check = new Check(Spec.MEMORY_DEREFERENCE);
		check.annotate(spec);
		return Collections.singletonList(spec);
	}

	/**
	 * Create an arithmetic expression from a pointer component (base or offset) and another expression.
	 *
	 * @param op
	 *            One of the comparison operators defined in {@link IASTBinaryExpression}.
	 * @returns The expression.
	 */
	private Expression constructPointerBinaryArithmeticExpression(final ILocation loc, final int op,
			final Expression left, final Expression right) {
		final CPrimitive cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();
		return mExpressionTranslation.constructArithmeticExpression(loc, op, left, cTypeOfPointerComponent, right,
				cTypeOfPointerComponent);
	}

	/**
	 * Compare a pointer component (base or offset) to another expression.
	 *
	 * @param op
	 *            One of the comparison operators defined in {@link IASTBinaryExpression}.
	 * @return The expression.
	 */
	private Expression constructPointerBinaryComparisonExpression(final ILocation loc, final int op,
			final Expression left, final Expression right) {
		final CPrimitive cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		return mExpressionTranslation.constructBinaryComparisonExpression(loc, op, left, cTypeOfPointerComponent, right,
				cTypeOfPointerComponent);
	}

	@Override
	public List<Statement> getChecksForFreeCall(final ILocation loc, final RValue pointerToBeFreed,
			final boolean isPointerCheckRequired, final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		assert pointerToBeFreed.getCType().getUnderlyingType() instanceof CPointer;

		if (!isPointerCheckRequired) {
			return Collections.emptyList();
		}

		final var cTypeOfPointerComponent = mExpressionTranslation.getCTypeOfPointerComponents();

		final Expression zeroNumericExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);

		final Expression valid = MemoryModelExpressionHelper.getValidArray(loc, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
		final Expression stackHeapBarrier = MemoryModelExpressionHelper.getStackHeapBarrier(loc,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);

		final Expression addrOffset = MemoryHandler.getPointerOffset(pointerToBeFreed.getValue(), loc);
		final Expression addrBase = MemoryHandler.getPointerBaseAddress(pointerToBeFreed.getValue(), loc);
		final Expression[] idcFree = { addrBase };

		final List<Statement> result = new ArrayList<>();

		/*
		 * creating the specification according to C99:7.20.3.2-2: The free function causes the space pointed to by ptr
		 * to be deallocated, that is, made available for further allocation. If ptr is a null pointer, no action
		 * occurs. Otherwise, if the argument does not match a pointer earlier returned by the calloc, malloc, or
		 * realloc function, or if the space has been deallocated by a call to free or realloc, the behavior is
		 * undefined.
		 */
		final Check check = new Check(Spec.MEMORY_FREE);

		// assert (~addr!offset == 0);
		final AssertStatement offsetZero = new AssertStatement(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, addrOffset, zeroNumericExpr));
		check.annotate(offsetZero);
		result.add(offsetZero);

		// assert (~addr!base < #StackHeapBarrier);
		final Expression inHeapArea =
				mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_lessThan,
						addrBase, cTypeOfPointerComponent, stackHeapBarrier, cTypeOfPointerComponent);
		final AssertStatement assertInHeapArea = new AssertStatement(loc, inHeapArea);
		check.annotate(assertInHeapArea);
		result.add(assertInHeapArea);

		// ~addr!base == 0
		final Expression isNullPtr =
				ExpressionFactory.newBinaryExpression(loc, Operator.COMPEQ, addrBase, zeroNumericExpr);

		// requires ~addr!base == 0 || #valid[~addr!base];
		final Expression addrIsValid = mBooleanArrayHelper
				.compareWithTrue(ExpressionFactory.constructNestedArrayAccessExpression(loc, valid, idcFree));
		final AssertStatement baseValid = new AssertStatement(loc,
				ExpressionFactory.newBinaryExpression(loc, Operator.LOGICOR, isNullPtr, addrIsValid));
		check.annotate(baseValid);
		result.add(baseValid);

		return result;
	}

	@Override
	public Expression createFunctionPointer(final ILocation loc, final BigInteger offset) {
		final Expression baseExpr = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), functionPointerPointerBaseValue);
		final Expression offsetExpr = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), offset);

		final Expression integerExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, mTypeSizeAndOffsetComputer.getSizeT(), offset);

		final Expression offsetMinus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, offsetExpr,
						mTypeSizeAndOffsetComputer.getSizeT(), integerExpr, mTypeSizeAndOffsetComputer.getSizeT());

		return MemoryHandler.constructPointerFromBaseAndOffset(baseExpr, offsetMinus, loc);

	}

	@Override
	public Expression addExpressionToPointer(final ILocation loc, final Expression ptrExpr, final Expression expr) {
		final Expression base = MemoryHandler.getPointerBaseAddress(ptrExpr, loc);
		final Expression offset = MemoryHandler.getPointerOffset(ptrExpr, loc);

		final Expression offsetPlus =
				mExpressionTranslation.constructArithmeticExpression(loc, IASTBinaryExpression.op_plus, offset,
						mTypeSizeAndOffsetComputer.getSizeT(), expr, mTypeSizeAndOffsetComputer.getSizeT());

		return MemoryHandler.constructPointerFromBaseAndOffset(base, offsetPlus, loc);
	}
}
