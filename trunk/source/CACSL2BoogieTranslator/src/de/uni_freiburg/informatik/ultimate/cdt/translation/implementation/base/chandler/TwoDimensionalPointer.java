package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class TwoDimensionalPointer extends BaseMemoryPointer {
	final BoogieType mComponentType;

	public TwoDimensionalPointer(final BoogieType componentType, final TypeSizes typeSizes) {
		super(typeSizes);
		mComponentType = componentType;

		mBoogieType = BoogieType.createStructType(new String[] { SFO.POINTER_BASE, SFO.POINTER_OFFSET },
				new BoogieType[] { mComponentType, mComponentType });
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
	public final Expression initialPointer(final ILocation loc, final BigInteger value,
			final CPrimitive cTypeOfPointerComponent) {
		final Expression baseExpr = mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, value);

		final Expression zeroExpr =
				mTypeSizes.constructLiteralForIntegerType(loc, cTypeOfPointerComponent, BigInteger.ZERO);

		return MemoryHandler.constructPointerFromBaseAndOffset(baseExpr, zeroExpr, loc);
	}
}
