package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;
import java.util.AbstractMap.SimpleEntry;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CTranslationUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.TranslationSettings;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.expressiontranslation.ExpressionTranslation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;

public class MemoryPointer1D extends MemoryPointerBase {
	final BoogieType mComponentType;

	/**
	 * The factory method that creates a OneDimensionalPointer instance. Ensures, that an instance is only created iff
	 * the settings are compatible.
	 *
	 * @return The instance.
	 */
	public static MemoryPointer1D create(final TranslationSettings settings, final BoogieType boogieType,
			final TypeSizes typeSizes) {
		final List<SimpleEntry<String, Boolean>> incompatibleOptions = List.of(
				new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_DEREF_VALIDITY,
						settings.checkPointerDerefValidity() != CheckMode.IGNORE),
				new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_CHECK_FREE_VALID,
						settings.checkIfFreedPointerIsValid()),
				new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_CHECK_MEMORY_LEAK_IN_MAIN,
						settings.checkMemoryLeakInMain()),
				new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_CHECK_POINTER_SUBTRACTION_AND_COMPARISON_VALIDITY,
						settings.getPointerSubtractionAndComparisonValidityCheckMode() != CheckMode.IGNORE),
				new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_CHECK_ALLOCATION_PURITY,
						settings.checkAllocationPurity()),
				new SimpleEntry<>(CACSLPreferenceInitializer.LABEL_USE_CONSTANT_ARRAYS, settings.useConstantArrays()));

		final List<String> incompatibleActiveOptions =
				incompatibleOptions.stream().filter(SimpleEntry::getValue).map(SimpleEntry::getKey).toList();

		if (!incompatibleActiveOptions.isEmpty()) {
			throw new UnsupportedOperationException(
					" The 1D memory addressing is not compatible with the following active settings: "
							+ String.join(", ", incompatibleActiveOptions));
		}

		return new MemoryPointer1D(boogieType, typeSizes);
	}

	private MemoryPointer1D(final BoogieType componentType, final TypeSizes typeSizes) {
		super(typeSizes);
		mComponentType = componentType;
		mBoogieType =
				BoogieType.createStructType(new String[] { SFO.POINTER_BASE }, new BoogieType[] { mComponentType });
	}

	@Override
	public BoogieType pointerType() {
		return mBoogieType;
	}

	@Override
	public Expression nullPointer(final ILocation loc, final CPrimitive cTypeOfPointerComponent) {
		return initialPointer(loc, BigInteger.ZERO, cTypeOfPointerComponent);
	}

	@Override
	public TypeDeclaration typeDeclaration(final ILocation loc) {
		final VarList fBase = new VarList(loc, new String[] { SFO.POINTER_BASE }, mComponentType.toASTType(loc));
		final VarList[] fields = { fBase };
		final BoogieType boogieType = BoogieType.createStructType(new String[] { SFO.POINTER_BASE },
				new BoogieType[] { (BoogieType) fBase.getType().getBoogieType() });
		final ASTType pointerType = new StructType(loc, boogieType, fields);
		// Pointer is non-finite, right? (ZxZ)..
		return new TypeDeclaration(loc, new Attribute[0], false, SFO.POINTER, new String[0], pointerType);
	}

	@Override
	public final Expression initialPointer(final ILocation loc, final BigInteger value,
			final CPrimitive cTypeOfPointerComponent) {
		final Expression baseExpr = mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, value);

		return createPointerFromBase(baseExpr, loc);
	}

	/**
	 * Creates a pointer from a base expression.
	 *
	 * @return The pointer.
	 */
	@SuppressWarnings("static-method")
	public Expression createPointerFromBase(final Expression base, final ILocation loc) {
		return ExpressionFactory.constructStructConstructor(loc, new String[] { SFO.POINTER_BASE },
				new Expression[] { base });
	}

	@Override
	public Expression pointerRelationExpression(final ILocation loc, final Expression baseEquality,
			final CheckMode mPointerSubtractionAndComparisonValidityCheckMode,
			final ExpressionTranslation expressionTranslation, final int op, final ExpressionResult left,
			final ExpressionResult right) {

		// The pointer relation is only dependent on the relation of base
		final Expression pointerRelation = constructPointerComponentRelation(loc, op, left.getLrValue().getValue(),
				right.getLrValue().getValue(), SFO.POINTER_BASE, expressionTranslation);

		switch (mPointerSubtractionAndComparisonValidityCheckMode) {
		case CHECK:
		case ASSUME:
			return ExpressionFactory.createBooleanLiteral(loc, true);
		case IGNORE:
			return pointerRelation;
		default:
			throw new AssertionError("unknown value");
		}
	}

	@Override
	public Expression constructPointerComponentRelation(final ILocation loc, final int op, final Expression leftPointer,
			final Expression rightPointer, final String component, final ExpressionTranslation expressionTranslation) {
		assert component.equals(SFO.POINTER_BASE) : "Illegal use of pointer component: " + component + " in 1D pointer";
		return pointerComponentRelation(loc, op, leftPointer, rightPointer, component, expressionTranslation);
	}

	@Override
	public boolean isNullPointer(final Expression ptr) {
		final StructConstructor sc = (StructConstructor) ptr;
		if (sc.getFieldValues().length == 1 && sc.getFieldIdentifiers()[0].equals(SFO.POINTER_BASE)
				&& BigInteger.ZERO.equals(CTranslationUtil.extractIntegerValue(sc.getFieldValues()[0]))) {
			return true;
		}

		return false;
	}
}
