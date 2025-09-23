package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public abstract class MemoryMetadataBase implements IMemoryMetadata {
	final ITypeHandler mTypeHandler;
	final ExpressionTranslation mExpressionTranslation;
	final IBooleanArrayHelper mBooleanArrayHelper;

	public MemoryMetadataBase(final ITypeHandler typeHandler, final ExpressionTranslation expressionTranslation,
			final IBooleanArrayHelper booleanArrayHelper) {
		mTypeHandler = typeHandler;
		mExpressionTranslation = expressionTranslation;
		mBooleanArrayHelper = booleanArrayHelper;
	}

	protected VariableDeclaration constructStackHeapBarrierConstant() {
		final ILocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		return new VariableDeclaration(ignoreLoc, new Attribute[0],
				new VarList[] { new VarList(ignoreLoc,
						new String[] { MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER.getName() },
						mTypeHandler.cType2AstType(ignoreLoc, mExpressionTranslation.getCTypeOfPointerComponents())) });
	}

	/**
	 * Returns the #StackHeapBarrier expression.
	 *
	 * @return The expression.
	 */
	public static Expression getStackHeapBarrier(final ILocation loc,
			final RequiredMemoryModelFeatures requiredMemoryModelFeatures,
			final MemoryModelDeclarationsHandler memoryModelDeclarationsHandler) {
		return MemoryModelExpressionHelper.getMemoryModelFeatureExpression(loc,
				MemoryModelDeclarations.ULTIMATE_STACK_HEAP_BARRIER, requiredMemoryModelFeatures,
				memoryModelDeclarationsHandler);
	}
}
