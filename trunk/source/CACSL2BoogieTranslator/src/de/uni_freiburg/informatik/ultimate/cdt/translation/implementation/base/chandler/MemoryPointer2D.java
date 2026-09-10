/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2025 Jan Körner
 * Copyright (C) 2015-2025 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
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
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.CheckMode;

/**
 * Representation of a memory pointer for a two-dimensional memory structure.
 *
 * The memory pointer is represented by a pair of values (base & offset) to address a memory location in a
 * two-dimensional memory structure.
 *
 * @author Jan Körner
 */
public final class MemoryPointer2D extends MemoryPointerBase {
	final BoogieType mComponentType;

	private MemoryPointer2D(final BoogieType componentType, final TypeSizes typeSizes) {
		super(typeSizes);
		mComponentType = componentType;
		mBoogieType = BoogieType.createStructType(new String[] { SFO.POINTER_BASE, SFO.POINTER_OFFSET },
				new BoogieType[] { mComponentType, mComponentType });
	}

	/**
	 * The factory method that creates a TwoDimensionalPointer instance.
	 *
	 * @return The instance.
	 */
	public static MemoryPointer2D create(final TranslationSettings settings, final BoogieType boogieType,
			final TypeSizes typeSizes) {
		return new MemoryPointer2D(boogieType, typeSizes);
	}

	@Override
	public BoogieType getPointerType() {
		return mBoogieType;
	}

	@Override
	public Expression constructNullPointer(final ILocation loc, final CPrimitive cTypeOfPointerComponent) {
		return constructInitialPointer(loc, BigInteger.ZERO, cTypeOfPointerComponent);
	}

	@Override
	public TypeDeclaration getTypeDeclaration(final ILocation loc) {
		final VarList fBase = new VarList(loc, new String[] { SFO.POINTER_BASE }, mComponentType.toASTType(loc));
		final VarList fOffset = new VarList(loc, new String[] { SFO.POINTER_OFFSET }, mComponentType.toASTType(loc));
		final VarList[] fields = { fBase, fOffset };
		final BoogieType boogieType =
				BoogieType.createStructType(new String[] { SFO.POINTER_BASE, SFO.POINTER_OFFSET }, new BoogieType[] {
						(BoogieType) fBase.getType().getBoogieType(), (BoogieType) fOffset.getType().getBoogieType() });
		final ASTType pointerType = new StructType(loc, boogieType, fields);
		// Pointer is non-finite, right? (ZxZ)..
		return new TypeDeclaration(loc, new Attribute[0], false, SFO.POINTER, new String[0], pointerType);
	}

	@Override
	public Expression constructInitialPointer(final ILocation loc, final BigInteger value,
			final CPrimitive cTypeOfPointerComponent) {
		final Expression baseExpr = mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, value);

		final Expression zeroExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);

		return constructPointerFromBaseAndOffset(baseExpr, zeroExpr, loc);
	}

	/**
	 * Returns the offset of a pointer.
	 *
	 * @return The offset.
	 */
	public Expression pointerOffset(final Expression pointer, final ILocation loc) {
		if (pointer instanceof final StructConstructor sc) {
			return sc.getFieldValues()[1];
		}
		return ExpressionFactory.constructStructAccessExpression(loc, pointer, SFO.POINTER_OFFSET);
	}

	/**
	 * Creates a pointer from a base and an offset.
	 *
	 * @return The pointer.
	 */
	public StructConstructor constructPointerFromBaseAndOffset(final Expression base, final Expression offset,
			final ILocation loc) {
		return ExpressionFactory.constructStructConstructor(loc, new String[] { SFO.POINTER_BASE, SFO.POINTER_OFFSET },
				new Expression[] { base, offset });
	}

	@Override
	public Expression constructPointerRelationExpression(final ILocation loc, final Expression baseEquality,
			final CheckMode mPointerSubtractionAndComparisonValidityCheckMode,
			final ExpressionTranslation expressionTranslation, final int op, final ExpressionResult left,
			final ExpressionResult right) {

		final Expression offsetRelation = constructPointerComponentRelation(loc, op, left.getLrValue().getValue(),
				right.getLrValue().getValue(), SFO.POINTER_OFFSET, expressionTranslation);

		return switch (mPointerSubtractionAndComparisonValidityCheckMode) {
		case CHECK, ASSUME -> offsetRelation;

		// use conjunction
		// TODO: Do not use conjunction. Use nondeterministic value if baseEquality does not hold.
		case IGNORE -> ExpressionFactory.newBinaryExpression(loc, Operator.LOGICAND, baseEquality, offsetRelation);
		};
	}

	@Override
	public Expression constructPointerComponentRelation(final ILocation loc, final int op, final Expression leftPointer,
			final Expression rightPointer, final String component, final ExpressionTranslation expressionTranslation) {
		assert component.equals(SFO.POINTER_BASE) || component.equals(SFO.POINTER_OFFSET) : "Unknown pointer component";
		return pointerComponentRelation(loc, op, leftPointer, rightPointer, component, expressionTranslation);
	}

	@Override
	public boolean isNullPointer(final Expression ptr) {
		return ptr instanceof final StructConstructor sc && sc.getFieldValues().length == 2
				&& sc.getFieldIdentifiers()[0].equals(SFO.POINTER_BASE)
				&& sc.getFieldIdentifiers()[1].equals(SFO.POINTER_OFFSET)
				&& BigInteger.ZERO.equals(CTranslationUtil.extractIntegerValue(sc.getFieldValues()[0]))
				&& BigInteger.ZERO.equals(CTranslationUtil.extractIntegerValue(sc.getFieldValues()[1]));
	}
}
