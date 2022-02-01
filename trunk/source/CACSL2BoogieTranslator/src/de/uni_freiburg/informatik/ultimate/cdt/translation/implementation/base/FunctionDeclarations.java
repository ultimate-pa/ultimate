/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Thomas Lang
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.LinkedHashMap;

import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.ITypeHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Collect function declarations for all functions that are used in the translation. During the translation we use one
 * object of this class. The object provides methods to construct function declarations. At the end of the translation
 * process all these function declarations should be added to the resulting Boogie program.
 *
 * @author Matthias Heizmann
 *
 */
public class FunctionDeclarations {

	/**
	 * Names of all bitwise operation that occurred in the program.
	 */
	private final LinkedHashMap<String, FunctionDeclaration> mDeclaredFunctions = new LinkedHashMap<>();
	private final ITypeHandler mTypeHandler;
	private final TypeSizes mTypeSizeConstants;
	public static final String BUILTIN_IDENTIFIER = "builtin";
	public static final String SMTDEFINED_IDENTIFIER = "smtdefined";
	public static final String OVERAPPROX_IDENTIFIER = "overapproximation";
	public static final String INDEX_IDENTIFIER = "indices";


	/**
	 * See {@link #finish()}.
	 */
	private boolean mIsFinished;

	public FunctionDeclarations(final ITypeHandler typeHandler, final TypeSizes typeSizeConstants) {
		super();
		mTypeHandler = typeHandler;
		mTypeSizeConstants = typeSizeConstants;
	}

	public void declareFunction(final ILocation loc, final String prefixedFunctionName, final Attribute[] attributes,
			final boolean boogieResultTypeBool, final CPrimitive resultCType, final CPrimitive... paramCTypes) {
		if (mIsFinished) {
			throw new AssertionError();
		}
		final ASTType resultASTType;
		if (boogieResultTypeBool) {
			resultASTType = new PrimitiveType(loc, BoogieType.TYPE_BOOL, SFO.BOOL);
		} else {
			resultASTType = mTypeHandler.cType2AstType(loc, resultCType);
		}
		final ASTType[] paramASTTypes = new ASTType[paramCTypes.length];
		for (int i = 0; i < paramCTypes.length; i++) {
			paramASTTypes[i] = mTypeHandler.cType2AstType(loc, paramCTypes[i]);
		}
		declareFunction(loc, prefixedFunctionName, attributes, resultASTType, paramASTTypes);
	}

	public void declareFunction(final ILocation loc, final String prefixedFunctionName, final Attribute[] attributes,
			final ASTType resultASTType, final ASTType... paramASTTypes) {
		if (mIsFinished) {
			throw new AssertionError();
		}
		// if (mDeclaredFunctions.containsKey(prefixedFunctionName)) {
		// return;
		// //throw new IllegalArgumentException("Function " + functionName + " already declared");
		// }
		if (!prefixedFunctionName.startsWith(SFO.AUXILIARY_FUNCTION_PREFIX)) {
			throw new IllegalArgumentException("Our convention says that user defined functions start with tilde");
		}

		final VarList[] inParams = new VarList[paramASTTypes.length];
		for (int i = 0; i < paramASTTypes.length; i++) {
			inParams[i] = new VarList(loc, new String[] { constructNameForFunctionInParam(i) }, paramASTTypes[i]);
		}
		final VarList outParam = new VarList(loc, new String[] { constructNameForFunctionOutParam() }, resultASTType);
		final FunctionDeclaration d =
				new FunctionDeclaration(loc, attributes, prefixedFunctionName, new String[0], inParams, outParam);
		mDeclaredFunctions.put(prefixedFunctionName, d);
	}

	/**
	 * (This class ({@link FunctionDeclarations}) does the naming of function parameters internally. This method exposes
	 *  the naming scheme to the outside.)
	 *
	 * @return the name that is used for the out parameter of all {@link FunctionDeclaration}s created by this class
	 */
	public static String constructNameForFunctionOutParam() {
		return "out";
	}

	/**
	 * (This class ({@link FunctionDeclarations}) does the naming of function parameters internally. This method exposes
	 *  the naming scheme to the outside.)
	 *
	 * @return the name that is used for the i-th in parameter of all {@link FunctionDeclaration}s created by this class
	 */
	public static String constructNameForFunctionInParam(final int i) {
		return "in" + i;
	}

	public LinkedHashMap<String, FunctionDeclaration> getDeclaredFunctions() {
		if (mIsFinished) {
			throw new AssertionError("since the map is modifiable we do not allow this query once this class is "
					+ "finished");
		}
		return mDeclaredFunctions;
	}

	public String computeBitvectorSuffix(final ILocation loc, final CPrimitive... paramCTypes) {
		final CPrimitive firstParam = paramCTypes[0];
		final Integer bytesize = mTypeSizeConstants.getSize(firstParam.getType());
		final int bitsize = bytesize * 8;

		return String.valueOf(bitsize);
	}

	/**
	 * Check if all CPrimitives in a sequence are equivalent.
	 *
	 * @return true iff all CPrimitives in cPrimitives are equivalent.
	 */
	public boolean checkParameters(final CPrimitive... cPrimitives) {
		final CPrimitives type = cPrimitives[0].getType();
		for (final CPrimitive t : cPrimitives) {
			if (!t.getType().equals(type)) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Simple locking mechanism to ensure that no function declarations are modified after the declarations have been
	 * added to the translation result.
	 */
	public void finish() {
		mIsFinished = true;
	}

}
