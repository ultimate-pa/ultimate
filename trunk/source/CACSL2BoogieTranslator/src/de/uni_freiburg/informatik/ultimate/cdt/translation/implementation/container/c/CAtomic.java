package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.util.Objects;

public class CAtomic extends CType {
	private final CType mUnderlyingType;

	public CAtomic(final CType underlyingType) {
		// FIXME: integrate those flags -- you will also need to change the equals method if you do
		super(false, false, false, false, false);
		mUnderlyingType = underlyingType;
	}

	@Override
	public CType getUnderlyingType() {
		return mUnderlyingType;
	}

	@Override
	public boolean isIncomplete() {
		return mUnderlyingType.isIncomplete();
	}

	@Override
	public boolean isIntegerType() {
		return mUnderlyingType.isIntegerType();
	}

	@Override
	public boolean isRealFloatingType() {
		return mUnderlyingType.isRealFloatingType();
	}

	@Override
	public boolean isComplexType() {
		return mUnderlyingType.isComplexType();
	}

	@Override
	public boolean isFloatingType() {
		return mUnderlyingType.isFloatingType();
	}

	@Override
	public boolean isRealType() {
		return mUnderlyingType.isRealType();
	}

	@Override
	public boolean isArithmeticType() {
		return mUnderlyingType.isArithmeticType();
	}

	@Override
	public boolean isScalarType() {
		return mUnderlyingType.isScalarType();
	}

	@Override
	public boolean isVoidType() {
		return mUnderlyingType.isVoidType();
	}

	@Override
	public String toString() {
		return "Atomic " + mUnderlyingType.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + Objects.hash(mUnderlyingType);
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!super.equals(obj) || getClass() != obj.getClass()) {
			return false;
		}
		return mUnderlyingType.equals(((CAtomic) obj).mUnderlyingType);
	}
}
