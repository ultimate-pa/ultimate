/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2018 University of Freiburg
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

import java.util.Arrays;

import org.eclipse.cdt.core.dom.ast.IArrayType;
import org.eclipse.cdt.core.dom.ast.IFunction;
import org.eclipse.cdt.core.dom.ast.IFunctionType;
import org.eclipse.cdt.core.dom.ast.IPointerType;
import org.eclipse.cdt.core.dom.ast.IType;
import org.eclipse.cdt.core.dom.ast.ITypedef;
import org.eclipse.cdt.core.dom.ast.IVariable;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.CDeclaration;

/**
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class CFunction extends CType {

	private final CType mResultType;

	private final CDeclaration[] mParamTypes;

	private final boolean mTakesVarArgs;

	public CFunction(final boolean isConst, final boolean isInline, final boolean isRestrict, final boolean isVolatile,
			final boolean isExtern, final CType resultType, final CDeclaration[] paramTypes,
			final boolean takesVarArgs) {
		super(isConst, isInline, isRestrict, isVolatile, isExtern);
		mResultType = resultType;
		mParamTypes = paramTypes;
		mTakesVarArgs = takesVarArgs;
	}

	/**
	 * Create a default CFunction without arguments and with int as return type.
	 */
	public static CFunction createDefaultCFunction() {
		return new CFunction(false, false, false, false, false, new CPrimitive(CPrimitives.INT), new CDeclaration[0],
				false);
	}

	/**
	 * Create an empty CFunction without arguments and with return type null
	 *
	 * TODO: This seems like a legacy method
	 */
	public static CFunction createEmptyCFunction() {
		return new CFunction(false, false, false, false, false, null, new CDeclaration[0], false);
	}

	public static CFunction createCFunction(final CType resultType, final CDeclaration[] paramDeclarations,
			final IFunction binding) {
		return new CFunction(false, binding.isInline(), false, false, binding.isExtern(), resultType, paramDeclarations,
				binding.takesVarArgs());
	}

	public static CFunction tryCreateCFunction(final CType resultType, final CDeclaration[] paramDeclarations,
			final ITypedef binding) {
		IType typedefType = binding.getType();
		if (typedefType instanceof IFunctionType) {
			return new CFunction(false, false, false, false, false, resultType, paramDeclarations,
					((IFunctionType) typedefType).takesVarArgs());
		}
		final IPointerType initialPointer;
		if (typedefType instanceof IPointerType) {
			initialPointer = (IPointerType) typedefType;
		} else {
			throw new UnsupportedOperationException("Cannot extract function type from typedef " + typedefType);
		}
		while (typedefType instanceof IPointerType) {
			typedefType = ((IPointerType) typedefType).getType();
		}
		if (typedefType instanceof IFunctionType) {
			return new CFunction(initialPointer.isConst(), false, initialPointer.isRestrict(),
					initialPointer.isVolatile(), false, resultType, paramDeclarations,
					((IFunctionType) typedefType).takesVarArgs());
		}
		throw new UnsupportedOperationException("Cannot extract function type from pointer to " + typedefType);
	}

	public static CFunction tryCreateCFunction(final CType resultType, final CDeclaration[] paramDeclarations,
			final IVariable binding) {
		IType varType = binding.getType();
		if (varType instanceof IPointerType) {
			// the initial type is already the pointer type
		} else if (varType instanceof IArrayType) {
			// its an array of function pointers -- find the value type
			while (varType instanceof IArrayType) {
				varType = ((IArrayType) varType).getType();
			}
			if (!(varType instanceof IPointerType)) {
				throw new UnsupportedOperationException(
						"Cannot extract function type from array of non-pointers " + varType);
			}
		} else {
			throw new UnsupportedOperationException("Cannot extract function type from variable " + varType);
		}
		final IPointerType initialPointer = (IPointerType) varType;
		while (varType instanceof IPointerType) {
			varType = ((IPointerType) varType).getType();
		}
		if (varType instanceof IFunctionType) {
			// it was indeed a function pointer
			return new CFunction(initialPointer.isConst(), false, initialPointer.isRestrict(),
					initialPointer.isVolatile(), binding.isExtern(), resultType, paramDeclarations,
					((IFunctionType) varType).takesVarArgs());
		}
		throw new UnsupportedOperationException("Cannot extract function type from pointer to " + varType);
	}

	/**
	 * Create a new {@link CFunction} that is identical to this one except for the parameter types.
	 */
	public CFunction newParameter(final CDeclaration[] newParamTypes) {
		return new CFunction(isConst(), isInline(), isRestrict(), isVolatile(), isExtern(), getResultType(),
				newParamTypes, takesVarArgs());
	}

	/**
	 * Create a new {@link CFunction} that is identical to this one except for the return type.
	 */
	public CFunction newReturnType(final CType returnType) {
		return new CFunction(isConst(), isInline(), isRestrict(), isVolatile(), isExtern(), returnType,
				getParameterTypes(), takesVarArgs());
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
		sb.append("((");
		for (int i = 0; i < mParamTypes.length; i++) {
			sb.append(mParamTypes[i].getType().toString());
			sb.append(" ");
		}
		if (mTakesVarArgs) {
			sb.append("...");
		}
		sb.append(")");
		sb.append(" : ");
		sb.append(mResultType.toString());
		sb.append(")");
		return sb.toString();
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
	public boolean isIncomplete() {
		// can a CFunction be incomplete? I never checked that carefully
		return false;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + Arrays.hashCode(mParamTypes);
		result = prime * result + ((mResultType == null) ? 0 : mResultType.hashCode());
		result = prime * result + (mTakesVarArgs ? 1231 : 1237);
		return result;
	}

	@Override
	public boolean equals(final Object o) {
		if (!(o instanceof CFunction)) {
			return false;
		}
		if (!super.equals(o)) {
			return false;
		}

		final CFunction other = (CFunction) o;
		if (mParamTypes.length != other.mParamTypes.length) {
			return false;
		}

		if (!mResultType.equals(other.mResultType)) {
			return false;
		}
		if (mTakesVarArgs != other.mTakesVarArgs) {
			return false;
		}

		for (int i = 0; i < mParamTypes.length; i++) {
			if (!mParamTypes[i].getType().equals(other.mParamTypes[i].getType())) {
				return false;
			}
		}

		return true;
	}

}
