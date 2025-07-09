package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.MemoryHandler.IBooleanArrayHelper;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;

/**
 * The memory model consisting of a MemoryAdressing and a MemoryStructure.
 */
public class MemoryModel {
	private final TypeSizes mTypeSizes;
	private final ITypeHandler mTypeHandler;
	private final IBooleanArrayHelper mBooleanArrayHelper;
	private final ExpressionTranslation mExpressionTranslation;

	private final IMemoryAdressing mMemoryAddressing;
	private final IMemoryStructure mMemoryStructure;

	public MemoryModel(final TranslationSettings settings, final TypeSizes typeSizes, final ITypeHandler typeHandler,
			final ExpressionTranslation exprTranslation, final IBooleanArrayHelper booleanArrayHelper) {
		mTypeSizes = typeSizes;
		mTypeHandler = typeHandler;
		mExpressionTranslation = exprTranslation;
		mBooleanArrayHelper = booleanArrayHelper;

		mMemoryAddressing = MemoryModelFactory.createMemoryAddressing(settings, mTypeHandler, mExpressionTranslation,
				mBooleanArrayHelper);
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
}
