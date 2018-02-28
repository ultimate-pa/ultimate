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

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 */
public class HeapDataArray {
	private final String mName;
	private final ASTType mContentASTType;
	private final int mSize;
	private final BoogieType mContentBoogieType;
	private final IdentifierExpression mIdentifierExpression;
	private final VariableLHS mVariableLhs;

	/**
	 *
	 * @param name
	 * @param aSTType
	 *            ast type of the memory contents
	 * @param contentBoogieType
	 *            boogie type of the memory contents
	 * @param pointerType
	 *            boogie type for pointers (used to build the type of the memory array)
	 * @param size
	 */
	public HeapDataArray(final String name, final ASTType aSTType, final BoogieType contentBoogieType,
			final BoogieType pointerType, final int size) {
		mName = name;
		mContentASTType = aSTType;
		mContentBoogieType = contentBoogieType;
		mSize = size;

		final BoogieArrayType arrayBoogieType =
				BoogieType.createArrayType(0, new BoogieType[] { pointerType }, contentBoogieType);

		mIdentifierExpression = ExpressionFactory.constructIdentifierExpression(LocationFactory.createIgnoreCLocation(),
				arrayBoogieType, getVariableName(), DeclarationInformation.DECLARATIONINFO_GLOBAL);
		mVariableLhs = ExpressionFactory.constructVariableLHS(LocationFactory.createIgnoreCLocation(), arrayBoogieType,
				getVariableName(), DeclarationInformation.DECLARATIONINFO_GLOBAL);
	}

	public String getName() {
		return mName;
	}

	public ASTType getASTType() {
		return mContentASTType;
	}

	public BoogieType getBoogieType() {
		return mContentBoogieType;
	}

	public String getVariableName() {
		return SFO.MEMORY + "_" + getName();
	}

	public IdentifierExpression getIdentifierExpression() {
		return mIdentifierExpression;
	}

	public VariableLHS getVariableLHS() {
		return mVariableLhs;
	}

	public int getSize() {
		return mSize;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mContentASTType == null) ? 0 : mContentASTType.hashCode());
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
		if (mContentASTType == null) {
			if (other.mContentASTType != null) {
				return false;
			}
		} else if (!mContentASTType.equals(other.mContentASTType)) {
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
		return "HeapDataArray [mName=" + mName + ", mASTType=" + mContentASTType + ", mSize=" + mSize + "]";
	}
}
