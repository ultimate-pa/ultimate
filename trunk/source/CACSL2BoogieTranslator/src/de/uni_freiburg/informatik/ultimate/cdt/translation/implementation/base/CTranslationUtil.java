/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.AuxVarInfo;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CArray;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CEnum;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CFunction;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CStruct;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CUnion;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionListResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResult;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultBuilder;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ExpressionResultTransformer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.INameHandler;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * Provides utility methods for the C to Boogie translation.
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class CTranslationUtil {

	private CTranslationUtil() {
		// don't instantiate this utility class
	}

	public static LocalLValue constructArrayAccessLhs(final ILocation loc, final LocalLValue arrayLhsToInitialize,
			final List<Integer> arrayIndex, final TypeSizes typeSizes) {
		final CArray cArrayType = (CArray) arrayLhsToInitialize.getCType().getUnderlyingType();

		final Expression[] index = new Expression[arrayIndex.size()];

		CArray currentArrayType = cArrayType;

		for (int i = 0; i < arrayIndex.size(); i++) {
			final CPrimitive currentIndexType = (CPrimitive) cArrayType.getBound().getCType().getUnderlyingType();
			index[i] = typeSizes.constructLiteralForIntegerType(loc, currentIndexType,
					new BigInteger(arrayIndex.get(i).toString()));

			final CType valueType = currentArrayType.getValueType().getUnderlyingType();
			if (valueType instanceof CArray) {
				currentArrayType = (CArray) valueType;
			} else {
				assert i == arrayIndex.size() - 1;
			}
		}

		final ArrayLHS alhs = ExpressionFactory.constructNestedArrayLHS(loc, arrayLhsToInitialize.getLhs(), index);

		return new LocalLValue(alhs, cArrayType.getValueType(), null);
	}

	public static LocalLValue constructArrayAccessLhs(final ILocation loc, final LocalLValue arrayLhsToInitialize,
			final Integer arrayIndex, final TypeSizes typeSizes) {
		final CArray cArrayType = (CArray) arrayLhsToInitialize.getCType().getUnderlyingType();

		final CPrimitive currentIndexType = (CPrimitive) cArrayType.getBound().getCType();
		final Expression index =
				typeSizes.constructLiteralForIntegerType(loc, currentIndexType, new BigInteger(arrayIndex.toString()));

		final ArrayLHS alhs = ExpressionFactory.constructNestedArrayLHS(loc, arrayLhsToInitialize.getLhs(),
				new Expression[] { index });

		final CType cellType = cArrayType.getValueType();

		return new LocalLValue(alhs, cellType, null);
	}

	public static boolean isVarlengthArray(final CArray cArrayType, final TypeSizes typeSizes, final IASTNode hook) {
		CArray currentArrayType = cArrayType;
		while (true) {
			if (typeSizes.extractIntegerValue(currentArrayType.getBound(), hook) == null) {
				// found a variable length bound
				return true;
			}
			final CType valueType = currentArrayType.getValueType().getUnderlyingType();
			if (valueType instanceof CArray) {
				currentArrayType = (CArray) valueType;
			} else {
				// reached at non-array type, found no varlength bound
				return false;
			}
		}
	}

	public static boolean isToplevelVarlengthArray(final CArray cArrayType, final TypeSizes typeSizes,
			final IASTNode hook) {
		return typeSizes.extractIntegerValue(cArrayType.getBound(), hook) == null;
	}

	public static List<Integer> getConstantDimensionsOfArray(final CArray cArrayType, final TypeSizes typeSizes,
			final IASTNode hook) {
		if (CTranslationUtil.isVarlengthArray(cArrayType, typeSizes, hook)) {
			throw new IllegalArgumentException("only call this for non-varlength array types");
		}
		CArray currentArrayType = cArrayType;

		final List<Integer> result = new ArrayList<>();
		while (true) {
			result.add(Integer
					.parseUnsignedInt(typeSizes.extractIntegerValue(currentArrayType.getBound(), hook).toString()));

			final CType valueType = currentArrayType.getValueType().getUnderlyingType();
			if (valueType instanceof CArray) {
				currentArrayType = (CArray) valueType;
			} else {
				return Collections.unmodifiableList(result);
			}
		}
	}

	/**
	 * According to 6.2.5.21 of C11 the structure types and the array types (but not
	 * the union types) are called aggregate types.
	 */
	public static boolean isAggregateType(final CType valueType) {
		return (valueType instanceof CStruct && !(valueType instanceof CUnion)) || valueType instanceof CArray;
	}

	public static int getConstantFirstDimensionOfArray(final CArray cArrayType, final TypeSizes typeSizes,
			final IASTNode hook) {
		final RValue dimRVal = cArrayType.getBound();

		final BigInteger extracted = typeSizes.extractIntegerValue(dimRVal, hook);
		if (extracted == null) {
			throw new IllegalArgumentException("only call this for non-varlength first dimension types");
		}

		final int dimInt = Integer.parseUnsignedInt(extracted.toString());
		return dimInt;
	}

	/**
	 * The given result must be an ExpressionResult or an ExpressionListResult. case ExpressionResult: the
	 * ExpressionResult is returned unchanged case ExpressionListResult: we evaluate all expressions, also switching to
	 * rvalue in every case, and we accumulate the corresponding statements in an ExpressionResult
	 *
	 * @param transformer
	 *            TODO
	 * @param loc
	 * @param result
	 *
	 * @return
	 */
	public static ExpressionResult convertExpressionListToExpressionResultIfNecessary(
			final ExpressionResultTransformer transformer, final ILocation loc, final Result result,
			final IASTNode hook) {
		assert result instanceof ExpressionListResult || result instanceof ExpressionResult;
		if (result instanceof ExpressionResult) {
			return (ExpressionResult) result;
		}
		final ExpressionListResult listResult = (ExpressionListResult) result;

		final ExpressionResultBuilder newResult = new ExpressionResultBuilder();

		for (final ExpressionResult elem : listResult.getList()) {
			/*
			 * Note: C11 6.5.17.2, footnote: A comma operator does not yield an lvalue. --> thus we can immediately
			 * switch to rvalue here
			 */
			newResult.addAllExceptLrValue(transformer.switchToRValueIfNecessary(elem, loc, hook));
		}
		newResult.setLrValue(listResult.getLast().getLrValue());
		return newResult.build();
	}

	public static int findIndexOfStructField(final CStruct targetCType, final String rootDesignator) {
		for (int i = 0; i < targetCType.getFieldCount(); i++) {
			if (targetCType.getFieldIds()[i].equals(rootDesignator)) {
				return i;
			}
		}
		throw new AssertionError("designator does not occur in struct type");
	}

	public static LocalLValue constructOffHeapStructAccessLhs(final ILocation loc,
			final LocalLValue structBaseLhsToInitialize, final int i) {
		final CStruct cStructType = (CStruct) structBaseLhsToInitialize.getCType().getUnderlyingType();

		final String fieldId = cStructType.getFieldIds()[i];

		final StructLHS lhs =
				ExpressionFactory.constructStructAccessLhs(loc, structBaseLhsToInitialize.getLhs(), fieldId);

		return new LocalLValue(lhs, cStructType.getFieldTypes()[i], null);
	}

	/**
	 * Generates a subexpression that allows accessing of a LHS in another expression (i.e., makes a
	 * StructAccessExpression out of a StructLHS, an identifier expression out of a VariableLHS, etc.)
	 */
	public static Expression convertLhsToExpression(final LeftHandSide lhs) {
		if (lhs instanceof VariableLHS) {
			final VariableLHS vlhs = (VariableLHS) lhs;
			return ExpressionFactory.constructIdentifierExpression(vlhs.getLoc(), (BoogieType) vlhs.getType(),
					vlhs.getIdentifier(), vlhs.getDeclarationInformation());
		} else if (lhs instanceof ArrayLHS) {
			final ArrayLHS alhs = (ArrayLHS) lhs;
			final Expression array = convertLhsToExpression(alhs.getArray());
			return ExpressionFactory.constructNestedArrayAccessExpression(alhs.getLocation(), array, alhs.getIndices());
		} else if (lhs instanceof StructLHS) {
			final StructLHS slhs = (StructLHS) lhs;
			final Expression struct = convertLhsToExpression(slhs.getStruct());
			return ExpressionFactory.constructStructAccessExpression(slhs.getLocation(), struct, slhs.getField());
		} else {
			throw new AssertionError("Strange LeftHandSide " + lhs);
		}
	}

	/**
	 * Create a havoc statement for each variable in auxVars. (Does not modify this auxVars map). We insert havocs for
	 * auxvars after the translation of a _statement_. This means that the Expressions carry the auxVarMap outside (via
	 * the ResultExpression they return), and that map is used for calling this procedure once we reach a (basic)
	 * statement.
	 *
	 * TODO: perhaps this could be integrated in ExpressionResultBuilder (i.e. a method that takes all auxvars, adds
	 * havocs for them, then resets the set of auxvars, and forbids adding further auxvars)
	 */
	public static List<HavocStatement> createHavocsForAuxVars(final Set<AuxVarInfo> auxVars) {
		final List<HavocStatement> result = new ArrayList<>();
		for (final AuxVarInfo auxvar : auxVars) {
			final HavocStatement havocStatement =
					new HavocStatement(auxvar.getVarDec().getLoc(), new VariableLHS[] { auxvar.getLhs() });
			result.add(havocStatement);
		}
		return Collections.unmodifiableList(result);
	}

	/**
	 * Returns true iff all auxvars in decls are contained in auxVars
	 */
	public static boolean isAuxVarMapComplete(final INameHandler nameHandler,
			final ExpressionResultBuilder resultBuilder) {
		return CTranslationUtil.isAuxVarMapComplete(nameHandler, resultBuilder.getDeclarations(),
				resultBuilder.getAuxVars());
	}

	/**
	 * Returns true iff all auxvars in decls are contained in auxVars
	 */
	public static boolean isAuxVarMapComplete(final INameHandler nameHandler, final List<Declaration> decls,
			// final Map<VariableDeclaration, ILocation> auxVars) {
			final Set<AuxVarInfo> auxVars) {
		boolean result = true;
		for (final Declaration rExprdecl : decls) {
			assert rExprdecl instanceof VariableDeclaration;
			final VariableDeclaration varDecl = (VariableDeclaration) rExprdecl;

			assert varDecl
					.getVariables().length == 1 : "there are never two auxvars declared in one declaration, right??";
			final VarList vl = varDecl.getVariables()[0];
			assert vl.getIdentifiers().length == 1 : "there are never two auxvars declared in one declaration, right??";
			final String id = vl.getIdentifiers()[0];

			if (nameHandler.isTempVar(id)) {
				// malloc auxvars do not need to be havocced in some cases (alloca)
				boolean auxVarExists = false;
				for (final AuxVarInfo auxVar : auxVars) {
					if (auxVar.getVarDec().equals(varDecl)) {
						auxVarExists = true;
						break;
					}
				}
				result &= auxVarExists;
			}
		}
		return result;
	}

	/**
	 * Convert the given expression to a corresponding LeftHandSide. This does not work for all kinds of Expressions, as
	 * not all have a corresponding LeftHandSide (e.g. ArrayStoreExpressions).
	 *
	 * @param modifiedGlobal
	 * @return
	 */
	public static LeftHandSide convertExpressionToLHS(final Expression expr) {
		if (expr instanceof IdentifierExpression) {
			final IdentifierExpression idex = (IdentifierExpression) expr;
			return ExpressionFactory.constructVariableLHS(idex.getLoc(), (BoogieType) idex.getType(),
					idex.getIdentifier(), idex.getDeclarationInformation());
		} else if (expr instanceof ArrayAccessExpression) {
			throw new UnsupportedOperationException("todo: implement");
		} else if (expr instanceof StructAccessExpression) {
			throw new UnsupportedOperationException("todo: implement");
		} else {
			throw new IllegalArgumentException("expression cannot be converted to a LeftHandSide: " + expr);
		}
	}

	/**
	 * Takes an arithmetic expression that has integer value and can be computed at compile-time, i.e., that contains no
	 * variables, and returns an IntegerLiteral containing the result.
	 *
	 * Matthias 2015-09-21: "premature optimization is the root of all evil" I think, by now we should not use this
	 * method and better live with long expressions. However, I don't want to delete this method, we might want to use
	 * it in the future.
	 */
	@Deprecated
	public static BigInteger computeConstantValue(final Expression value) {
		if (value instanceof IntegerLiteral) {
			return new BigInteger(((IntegerLiteral) value).getValue());
		} else if (value instanceof UnaryExpression) {
			switch (((UnaryExpression) value).getOperator()) {
			case ARITHNEGATIVE:
				return computeConstantValue(((UnaryExpression) value).getExpr()).negate();
			default:
				throw new UnsupportedOperationException("could not compute constant value");
			}
		} else if (value instanceof BinaryExpression) {
			switch (((BinaryExpression) value).getOperator()) {
			case ARITHDIV:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.divide(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMINUS:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.subtract(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMOD:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.mod(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHMUL:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.multiply(computeConstantValue(((BinaryExpression) value).getRight()));
			case ARITHPLUS:
				return computeConstantValue(((BinaryExpression) value).getLeft())
						.add(computeConstantValue(((BinaryExpression) value).getRight()));
			default:
				throw new UnsupportedOperationException("could not compute constant value");
			}
		} else {
			throw new UnsupportedOperationException("could not compute constant value");
		}
	}

	public static boolean isAggregateCType(final CType cTypeRaw) {
		final CType cType = cTypeRaw.getUnderlyingType();

		if (cType instanceof CPrimitive || cType instanceof CEnum || cType instanceof CPointer
				|| cType instanceof CUnion || cType instanceof CFunction) {
			return false;
		} else if (cType instanceof CArray || cType instanceof CStruct) {
			return true;
		} else {
			throw new UnsupportedOperationException("missed a type??");
		}
	}

	/**
	 * Returns the value of an expression in case the expression is a literal.
	 * </p>
	 * Warning: This method is not suitable for obtaining the value of C
	 * expressions. If you also want to get integer values of constants (in the
	 * sense of variables that got statically some value assigned) then use
	 * {@link TypeSizes#extractIntegerValue(Expression, CType, IASTNode)}
	 *
	 */
	public static BigInteger extractIntegerValue(final Expression expr) {
		BigInteger result;
		if (expr instanceof IntegerLiteral) {
			result = new BigInteger(((IntegerLiteral) expr).getValue());
		} else if (expr instanceof BitvecLiteral) {
			result = new BigInteger(((BitvecLiteral) expr).getValue());
		} else {
			result = null;
		}
		return result;
	}
}
