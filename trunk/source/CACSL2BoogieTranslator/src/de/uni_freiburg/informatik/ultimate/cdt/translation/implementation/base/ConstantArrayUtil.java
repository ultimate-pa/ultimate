/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructExpanderUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.LocationFactory;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public final class ConstantArrayUtil {
	private ConstantArrayUtil() {
		// don't instantiate this utility class
	}

	public static Expression getConstantArray(final FunctionDeclarations decls, final ILocation loc,
			final BoogieArrayType arrayType, final Expression constant) {
		assert arrayType.getValueType().equals(constant.getType()) : "constant array of type " + arrayType
				+ " cannot have constant value " + constant;
		final FunctionDeclaration function = getOrDeclareConstantArrayFunction(decls, arrayType);
		return new FunctionApplication(loc, arrayType, function.getIdentifier(), new Expression[] { constant });
	}

	public static FunctionDeclaration getOrDeclareZeroArrayFunction(final FunctionDeclarations decls,
			final BoogieArrayType type) {
		return getOrDeclareConstantArrayFunction(decls, type, "", new BoogieType[0],
				CTranslationUtil::getSmtZeroStringForBoogieType);
	}

	public static FunctionDeclaration getOrDeclareConstantArrayFunction(final FunctionDeclarations decls,
			final BoogieArrayType type) {
		return getOrDeclareConstantArrayFunction(decls, type, "~param", new BoogieType[] { type.getValueType() },
				valType -> {
					assert valType.equals(type.getValueType()) : "constant value of type " + type.getValueType()
							+ " cannot be used for " + valType;
					return FunctionDeclarations.constructNameForFunctionInParam(0);
				});
	}

	private static FunctionDeclaration getOrDeclareConstantArrayFunction(final FunctionDeclarations decls,
			final BoogieArrayType type, final String suffix, final BoogieType[] params,
			final Function<BoogieType, String> getConstantValue) {
		final String name = getFunctionName(type, suffix);
		final FunctionDeclaration old = decls.getDeclaredFunctions().get(name);
		if (old != null) {
			assert paramTypesMatch(params, old);
			return old;
		}

		return constructAndRegisterDeclaration(decls, type, name, params, getConstantValue);
	}

	private static boolean paramTypesMatch(final BoogieType[] params, final FunctionDeclaration old) {
		int i = 0;
		for (final VarList vl : old.getInParams()) {
			for (final String x : vl.getIdentifiers()) {
				assert i < params.length : "parameter count differs";
				assert params[i].equals(vl.getType().getBoogieType()) : "type of parameter " + x + " differs";
				i++;
			}
		}
		return true;
	}

	private static FunctionDeclaration constructAndRegisterDeclaration(final FunctionDeclarations decls,
			final BoogieArrayType boogieType, final String functionName, final BoogieType[] params,
			final Function<BoogieType, String> getConstantValue) {
		final CACSLLocation ignoreLoc = LocationFactory.createIgnoreCLocation();
		final List<Attribute> attributeList = new ArrayList<>();

		final BoogieType ft = StructExpanderUtil.flattenType(boogieType, new HashMap<>(), new HashMap<>());
		if (ft instanceof BoogieStructType) {
			final BoogieStructType bst = (BoogieStructType) ft;
			for (int fieldNr = 0; fieldNr < bst.getFieldCount(); fieldNr++) {
				// add expand attribute
				final NamedAttribute expandAttribute =
						new NamedAttribute(ignoreLoc, StructExpanderUtil.ATTRIBUTE_EXPAND_STRUCT, new Expression[] {
								ExpressionFactory.createStringLiteral(ignoreLoc, bst.getFieldIds()[fieldNr]) });
				attributeList.add(expandAttribute);
				attributeList.add(createSmtDefinedAttribute(ignoreLoc, (BoogieArrayType) bst.getFieldType(fieldNr),
						getConstantValue));
			}
		} else {
			attributeList.add(createSmtDefinedAttribute(ignoreLoc, boogieType, getConstantValue));
		}

		final Attribute[] attributes = attributeList.toArray(new Attribute[attributeList.size()]);

		// register the FunctionDeclaration
		final ASTType[] astParams = Arrays.stream(params).map(x -> x.toASTType(ignoreLoc)).toArray(ASTType[]::new);
		return decls.declareFunction(ignoreLoc, functionName, attributes, boogieType.toASTType(ignoreLoc), astParams);
	}

	private static NamedAttribute createSmtDefinedAttribute(final ILocation loc, final BoogieArrayType type,
			final Function<BoogieType, String> getConstantValue) {
		// build something like "((as const (Array (Array Int Int))) ((as const (Array Int Int)) 0))";
		final String smtDefinition = getSmtConstantArrayStringForBoogieType(type, getConstantValue);

		return new NamedAttribute(loc, FunctionDeclarations.SMTDEFINED_IDENTIFIER,
				new Expression[] { ExpressionFactory.createStringLiteral(loc, smtDefinition) });
	}

	private static String getSmtConstantArrayStringForBoogieType(final BoogieArrayType boogieArrayType,
			final Function<BoogieType, String> getConstantValue) {
		String currentArray;
		if (boogieArrayType.getValueType() instanceof BoogieArrayType) {
			currentArray = getSmtConstantArrayStringForBoogieType((BoogieArrayType) boogieArrayType.getValueType(),
					getConstantValue);
		} else {
			currentArray = getConstantValue.apply(boogieArrayType.getValueType());
		}
		String currentTypeString = CTranslationUtil.getSmtSortStringForBoogieType(boogieArrayType.getValueType());
		for (int i = boogieArrayType.getIndexCount() - 1; i >= 0; i--) {
			currentTypeString = String.format("(Array %s %s)",
					CTranslationUtil.getSmtSortStringForBoogieType(boogieArrayType.getIndexType(i)), currentTypeString);
			currentArray = String.format("((as const %s) %s)", currentTypeString, currentArray);
		}
		return currentArray;
	}

	private static String getFunctionName(final BoogieType boogieArrayType, final String suffix) {
		/*
		 * "~RB~" stands for "right bracket", "~RC~" stands for "right curly brace", "~COM~" stands for "comma", "~COL~"
		 * stands for "colon", if there is a nicer naming that still avoids name clashes, that naming should be used.
		 */
		final String sanitizedTypeName = boogieArrayType.toString().replace(":", "~COL~").replace(", ", "~COM~")
				.replace("{ ", "~LC~").replace(" }", "~RC~").replace("]", "~RB~").replace("[", "~LB~");
		return SFO.AUXILIARY_FUNCTION_PREFIX + "const~array~" + sanitizedTypeName + suffix;
	}
}
