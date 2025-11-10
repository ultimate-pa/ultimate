package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class MemoryMetadataDefault2D extends MemoryMetadataBase {

	public MemoryMetadataDefault2D(final ITypeHandler typeHandler, final ExpressionTranslation expressionTranslation,
			final IBooleanArrayHelper booleanArrayHelper) {
		super(typeHandler, expressionTranslation, booleanArrayHelper);
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
	public List<MemoryModelDeclarations> getMetaDataDeclarations() {
		return List.of(MemoryModelDeclarations.ULTIMATE_VALID, MemoryModelDeclarations.ULTIMATE_LENGTH);
	}

	/**
	 * Returns the #valid array expression.
	 *
	 * @return The expression.
	 */
	public static Expression getValidArray(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return MemoryModelExpressionHelper.getMemoryModelFeatureExpression(loc, MemoryModelDeclarations.ULTIMATE_VALID,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

	/**
	 * Returns the #valid array as an lhs variable.
	 *
	 * @return The variable.
	 */
	public static VariableLHS getValidArrayLhs(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return MemoryModelExpressionHelper.getMemoryModelFeatureLhs(loc, MemoryModelDeclarations.ULTIMATE_VALID,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}

	/**
	 * Returns the #length array expression.
	 *
	 * @return The expression.
	 */
	public static Expression getLengthArray(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return MemoryModelExpressionHelper.getMemoryModelFeatureExpression(loc, MemoryModelDeclarations.ULTIMATE_LENGTH,
				requiredMemoryModelFeatures, memoryModelDeclarationsHandler);
	}
}
