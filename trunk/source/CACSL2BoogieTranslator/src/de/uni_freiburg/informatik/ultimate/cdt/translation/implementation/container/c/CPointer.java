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
/**
 * Describes a pointer given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public class CPointer extends CType {
	/**
	 * The type, this pointer points to.
	 */
	private final CType mPointsToType;

	/**
	 * Constructor.
	 *
	 * @param pointsToType
	 *            the type, this pointer points to.
	 */
	public CPointer(final CType pointsToType) {
		// FIXME: integrate those flags
		super(false, false, false, false);
		mPointsToType = pointsToType;
	}

	public CType getPointsToType() {
		return mPointsToType;
	}

	@Override
	public String toString() {
		return SFO.POINTER;
	}

	@Override
	public boolean equals(final Object o) {
		if (this == o) {
			return true;
		}
		if (!(o instanceof CType)) {
			return false;
		}
		final CType oType = ((CType) o).getUnderlyingType();
		if (oType instanceof CPointer) {
			return mPointsToType.equals(((CPointer) oType).mPointsToType);
		}
		return false;
	}

	@Override
	public boolean isCompatibleWith(final CType o) {
		if (o instanceof CPointer && ((CPointer) o).mPointsToType instanceof CPrimitive
				&& ((CPrimitive) ((CPointer) o).mPointsToType).getType() == CPrimitives.VOID) {
			return true;
		}

		if (super.equals(o)) {
			return true;
		}
		final CType oType = o.getUnderlyingType();
		if (oType instanceof CPointer) {
			return mPointsToType.isCompatibleWith(((CPointer) oType).mPointsToType);
		}
		return false;
	}

	public CType getTargetType() {
		return mPointsToType;
	}

	@Override
	public int hashCode() {
		return HashUtils.hashJenkins(31, mPointsToType);
	}
}
