/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.util.CoreUtil;

/**
 * Pointer type (see C11 6.2.5.20.5)
 *
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public final class CPointer implements ICType {
	/**
	 * The type, this pointer points to.
	 */
	private final ICType mPointsToType;

	/**
	 * Constructor.
	 *
	 * @param pointsToType
	 *            the type, this pointer points to.
	 */
	public CPointer(final ICType pointsToType) {
		mPointsToType = pointsToType;
	}

	public ICType getPointsToType() {
		return mPointsToType;
	}

	@Override
	public boolean isIncomplete() {
		// pointer is never incomplete - even if it points to an incomplete type!
		return false;
	}

	@Override
	public String toString() {
		CPointer pointer = this;
		ICType pointsTo = null;
		int i = 1;
		while (true) {
			pointsTo = pointer.getPointsToType();
			if (pointsTo instanceof CPointer) {
				pointer = (CPointer) pointsTo;
				i++;
			} else {
				break;
			}
		}

		if (pointsTo instanceof CStructOrUnion) {
			return CoreUtil.repeat(i, "*") + ((CStructOrUnion) pointsTo).getName();
		}
		return CoreUtil.repeat(i, "*") + pointsTo.toString();
	}

	@Override
	public int hashCode() {
		return Objects.hash(mPointsToType);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		return Objects.equals(mPointsToType, ((CPointer) obj).mPointsToType);
	}

	@Override
	public boolean isAtomic() {
		return false;
	}

	@Override
	public boolean isScalarType() {
		return true;
	}

	@Override
	public boolean isVoidPointerType() {
		return mPointsToType.getUnderlyingType().isVoidType();
	}

	/**
	 * Factory method to create a representation of the <code>void*</code> type.
	 *
	 * @return the void pointer type
	 */
	public static CPointer voidPointer() {
		return new CPointer(new CPrimitive(CPrimitive.CPrimitives.VOID));
	}
}
