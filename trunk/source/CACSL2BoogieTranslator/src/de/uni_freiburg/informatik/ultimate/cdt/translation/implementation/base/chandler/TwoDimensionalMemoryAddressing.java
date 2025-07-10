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
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * The two dimensional memory addressing.
 */
public class TwoDimensionalMemoryAddressing extends BaseMemoryAdressing {

	public TwoDimensionalMemoryAddressing(final ITypeHandler typeHandler, final ExpressionTranslation exprTranslation,
			final IBooleanArrayHelper booleanArrayHelper, final TypeSizes typeSizes) {
		super(typeHandler, exprTranslation, booleanArrayHelper, typeSizes);
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
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		final List<Statement> statements = new ArrayList();
		// TODO 20211115 Matthias: added the following assume-base initialization for
		// #valid[0] == 0. I presume that the assignment-case initialization is not
		// needed in any approach and can be dropped.
		if (true) {
			// assume #valid[0] == 0 (i.e., the memory at the NULL-pointer is
			// not allocated)
			final Expression zero = mTypeSizes.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
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
			final Expression zero = mTypeSizes.constructLiteralForIntegerType(loc,
					mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
			final Expression literalThatRepresentsFalse = mBooleanArrayHelper.constructFalse();
			final AssignmentStatement assignment = MemoryHandler.constructOneDimensionalArrayUpdate(loc, zero,
					MemoryModelExpressionHelper.getValidArrayLhs(loc, requiredMemoryModelFeatures,
							memoryModelDeclarationsHandler),
					literalThatRepresentsFalse);

			statements.add(assignment);
		}

		// Add assume(0 < #StackHeapBarrier) to ensure that the null
		// pointer is on the heap.
		final Expression zero = mTypeSizes.constructLiteralForIntegerType(loc,
				mExpressionTranslation.getCTypeOfPointerComponents(), BigInteger.ZERO);
		final Expression zeroSmallerStackHeapBarrier =
				mExpressionTranslation.constructBinaryComparisonIntegerExpression(loc, IASTBinaryExpression.op_lessThan,
						zero, mExpressionTranslation.getCTypeOfPointerComponents(), MemoryModelExpressionHelper
								.getStackHeapBarrier(loc, requiredMemoryModelFeatures, memoryModelDeclarationsHandler),
						mExpressionTranslation.getCTypeOfPointerComponents());

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
}
