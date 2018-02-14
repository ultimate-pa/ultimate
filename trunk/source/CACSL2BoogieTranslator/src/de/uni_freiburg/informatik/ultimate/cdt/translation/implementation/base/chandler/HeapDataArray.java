/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
 * Instances of this class define a memory model.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class HeapDataArray {
	private final String mName;
	private final ASTType mASTType;
	private final int mSize;
	private final BoogieType mBoogieType;
	public HeapDataArray(final String name, final ASTType aSTType, final BoogieType boogieType, final int size) {
		super();
		mName = name;
		mASTType = aSTType;
		mBoogieType = boogieType;
		mSize = size;
	}
	public String getName() {
		return mName;
	}
	public ASTType getASTType() {
		return mASTType;
	}
	public BoogieType getBoogieType() {
		return mBoogieType;
	}
	public String getVariableName() {
		return SFO.MEMORY + "_" + getName();
	}
	public int getSize() {
		return mSize;
	}
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mASTType == null) ? 0 : mASTType.hashCode());
		result = prime * result + ((mName == null) ? 0 : mName.hashCode());
		result = prime * result + mSize;
		return result;
	}
	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final HeapDataArray other = (HeapDataArray) obj;
		if (mASTType == null) {
			if (other.mASTType != null) {
				return false;
			}
		} else if (!mASTType.equals(other.mASTType)) {
			return false;
		}
		if (mName == null) {
			if (other.mName != null) {
				return false;
			}
		} else if (!mName.equals(other.mName)) {
			return false;
		}
		return mSize == other.mSize;
	}
	@Override
	public String toString() {
		return "HeapDataArray [mName=" + mName + ", mASTType=" + mASTType + ", mSize=" + mSize + "]";
	}



}
