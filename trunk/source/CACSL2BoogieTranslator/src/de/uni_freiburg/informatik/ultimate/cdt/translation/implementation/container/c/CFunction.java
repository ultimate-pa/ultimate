/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;
import de.uni_freiburg.informatik.ultimate.util.HashUtils;

public class CFunction extends CType {

	private final CType mResultType;

	private final CDeclaration[] mParamTypes;

	private final boolean mTakesVarArgs;

	public CFunction(final CType resultType, final CDeclaration[] paramTypes, final boolean takesVarArgs) {
		super(false, false, false, false); // FIXME: integrate those flags
		mResultType = resultType;
		mParamTypes = paramTypes;
		mTakesVarArgs = takesVarArgs;
	}

	public CType getResultType() {
		return mResultType;
	}

	public CDeclaration[] getParameterTypes() {
		return mParamTypes;
	}

	public boolean takesVarArgs() {
		return mTakesVarArgs;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("CFunction: ");
		String times = "";
		for (int i = 0; i < mParamTypes.length; i++) {
			sb.append(times);
			sb.append(mParamTypes[i].getType().toString());
			times = " x ";
		}
		if (mTakesVarArgs) {
			sb.append(" x ...");
		}
		sb.append(" -> ");
		sb.append(mResultType.toString());
		return sb.toString();
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof CFunction)) {
			return false;
		}
		final CFunction other = (CFunction) o;
		if (mParamTypes.length != other.mParamTypes.length) {
			return false;
		}
		boolean result = true;
		result &= mResultType.equals(other.mResultType);
		for (int i = 0; i < mParamTypes.length; i++) {
			result &= mParamTypes[i].getType().equals(other.mParamTypes[i].getType());
		}
		result &= mTakesVarArgs == other.mTakesVarArgs;
		return result;
	}

	public String functionSignatureAsProcedureName() {
		final StringBuilder sb = new StringBuilder();
		sb.append("##fun~");
		String times = "";
		for (int i = 0; i < mParamTypes.length; i++) {
			sb.append(times);
			sb.append(mParamTypes[i].getType().getUnderlyingType().toString());
			times = "~X~";
		}
		if (mTakesVarArgs) {
			sb.append("X~varArgs~");
		}
		sb.append("~TO~");
		sb.append(mResultType.getUnderlyingType().toString());
		return sb.toString();
	}

	@Override
	public boolean isCompatibleWith(final CType o) {
		if (o instanceof CPrimitive && ((CPrimitive) o).getType() == CPrimitives.VOID) {
			return true;
		}

		if (!(o instanceof CFunction)) {
			return false;
		}
		final CFunction other = (CFunction) o;
		if (mParamTypes.length != other.mParamTypes.length) {
			return false;
		}
		boolean result = true;
		result &= mResultType.isCompatibleWith(other.mResultType);
		for (int i = 0; i < mParamTypes.length; i++) {
			result &= mParamTypes[i].getType().isCompatibleWith(other.mParamTypes[i].getType());
		}
		result &= mTakesVarArgs == other.mTakesVarArgs;
		return result;
	}

	@Override
	public int hashCode() {
		int result = HashUtils.hashJenkins(31, mResultType);
		final CType[] pTypes = new CType[mParamTypes.length];
		for (int i = 0; i < pTypes.length; i++) {
			result = HashUtils.hashJenkins(result, mParamTypes[i].getType());
		}
		result = HashUtils.hashJenkins(result, mTakesVarArgs);
		return result;
	}
}
