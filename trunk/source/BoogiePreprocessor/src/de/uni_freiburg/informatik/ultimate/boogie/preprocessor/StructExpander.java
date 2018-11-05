/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Jochen Hoenicke (hoenicke@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BoogiePreprocessor plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
/**
 * Class that handles expanding of structs into normal variables.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.boogie.CachingBoogieTransformer;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ConstDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.NamedAttribute;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StringLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePlaceholderType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieStructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieTypeConstructor;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ModelUtils;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

/**
 * This class removes our Boogie syntax extension of structs and creates a plain Boogie code without the struct
 * extension.
 *
 * The extensions for struct we support are: New ASTType:
 *
 * <pre>
 * StructType ::= fields : VarList[]
 *
 * <pre>
 *
 * New LeftHandSide:
 *
 * <pre>
 * StructLHS ::=  struct: LeftHandSide, field:String
 * </pre>
 *
 * New Expressions:
 *
 * <pre>
 * StructAccessExpression ::=  struct : Expression, field:String
 * StructConstructor ::= fieldIdentifiers : String[], fieldValues : Expression[]
 * </pre>
 *
 * Also, IdentifierExpression and VariableLHS can refer to struct typed variables. And functions can take struct typed
 * parameters and return struct typed values.
 *
 * The semantic type of a boogie.ast.StructType is represented by boogie.type.StructType. This contains an array of
 * fieldNames (String) and an array of fieldTypes (BoogieType) of the same length. Two struct types are identical if
 * they declare the same names of the same types in the same order. The field types can also be struct typed and one can
 * build arrays over structs and structs over arrays.
 *
 * This class gets rid of structs by flattening them and replacing them by the finite list of values.
 *
 * If a struct type is used as index type of an array, it is replaced by a multidimensional array, one index type for
 * every element in the struct, forgetting the names of the fields. E.g., <code>[{a:int,b:real]int</code> is transformed
 * to <code>[int,real]int</code> If a struct type is used as element type of an array, the struct is pulled to the
 * outside, hence it is a struct of arrays, all with the same index type and the element type of the corresponding
 * field. E.g., <code>[int]{a:int,b:real}</code> is transformed to <code>{a:[int]int, b:[int]real}</code> A struct type
 * in a struct is flattened and the field names are combined with DOT. e.g. the type
 * <code>{ a : int, b: { x:int, y:int}}</code> is flattened to <code>{ a: int, b.x : int, b.y : int}</code>. After these
 * transformation a type can contain a struct type only on the outside.
 *
 * For every variable declaration occuring in the BoogieAST with a struct type, we create one variable for each field,
 * e.g. <code>var x,y: {a:int,b:real}, z:real;<code>
 * is transformed to
 * <code>var x.a:int, x.b:real, y.a:int, y.b:real, z:real</code>. This also includes the variable lists used for input
 * parameters in function and procedure declarations and for output parameters in procedures.
 *
 * A function returning a struct is replaced by several functions, one for each field. The name also uses the DOT, e.g.,
 * <code>function f () : {a:int,b:real}<code> is expanded to <code>function f.a () : int; function f.b():real}<code>
 *
 * In assignments and procedure calls (which are also assignments), the left-hand-sides that are of struct type are
 * expanded to a list of left-hand-sides, one for each field. An expression of a struct type is replaced by a list of
 * expressions one for each field.
 *
 * The expansion of expression of struct types works as follows: An IdentifierExpression is expanded to one
 * IdentifierExpression for every field, matching the way the variable declaration is expanded. An FunctionApplication
 * is expanded into a list of FunctionApplication one for each field. The function parameters are just duplicated. An
 * array access is expanded recursively, e.g., if <code>expr<code> expands to <code>e1,...,en<code>, <code>expr[i]<code>
 * expands to <code>e1[i],...,en[i]<code>
 *
 *
 *
 * @author Markus Lindenmann, Jochen Hoenicke
 * @date 26.08.2012
 */
public class StructExpander extends CachingBoogieTransformer implements IUnmanagedObserver {
	private static final String ATTRIBUTE_EXPAND_STRUCT = "expand_struct";

	/**
	 * String holding a period / dot.
	 */
	private static final String DOT = ".";

	/**
	 * The cache used by flattenType to prevent repeated work.
	 */
	private final HashMap<BoogieType, BoogieType> mFlattenCache;
	/**
	 * This map remembers the created struct types. For named type parameters that have struct type, we create a new
	 * pseudo type struct~f1~f2, where f1,f2 are the names of the field and that takes the types of f1 and f2 as
	 * parameters. This is used to instantiate these type parameters. E.g. the type <code>Field {a:int, b:real}</code>
	 * is flattened to <code>Field (struct~a~b int real)</code>. We need to remember to add the type declaration
	 *
	 * <pre>
	 * type struct~a~b $0 $1;
	 * </pre>
	 *
	 * which is remembered in this map.
	 */
	private final HashMap<String, BoogieTypeConstructor> mStructTypes;

	private final BoogiePreprocessorBacktranslator mTranslator;

	protected StructExpander(final BoogiePreprocessorBacktranslator translator, final ILogger logger) {
		mTranslator = translator;
		mFlattenCache = new HashMap<>();
		mStructTypes = new HashMap<>();
	}

	/**
	 * Create a new struct wrapper type and register the corresponding type constructor, unless that is already present.
	 * The input type must already be flattened, i.e., the field types do not contain any structs.
	 *
	 * @param st
	 *            the struct type for which a wrapper is created.
	 * @returns a new constructed type for this struct type.
	 */
	private BoogieType createStructWrapperType(final BoogieStructType st) {
		final StringBuilder sb = new StringBuilder();
		sb.append("struct");
		for (final String f : st.getFieldIds()) {
			sb.append('~').append(f);
		}
		final String name = sb.toString();
		BoogieTypeConstructor tc = mStructTypes.get(name);
		if (tc == null) {
			final int[] paramOrder = new int[st.getFieldCount()];
			for (int i = 0; i < paramOrder.length; i++) {
				paramOrder[i] = i;
			}
			tc = new BoogieTypeConstructor(name, false, st.getFieldCount(), paramOrder);
			mStructTypes.put(name, tc);
		}
		final BoogieType[] types = new BoogieType[st.getFieldCount()];
		for (int i = 0; i < types.length; i++) {
			types[i] = st.getFieldType(i);
		}
		return BoogieType.createConstructedType(tc, types);
	}

	/**
	 * Convert a type to a flattened type, where there is a single struct type at the outside. arrays of structs are
	 * converted to structs of arrays and nested structs are flattened. We work on BoogieType and use
	 * getUnderlyingType() so that we do not need to handle type aliases.
	 *
	 * @param itype
	 *            the type that should be flattened. This must be a BoogieType, but we want to avoid casts everywhere.
	 * @return the flattened type as BoogieType.
	 */
	private BoogieType flattenType(final IBoogieType itype) {
		BoogieType result;
		final BoogieType type = ((BoogieType) itype).getUnderlyingType();
		if (mFlattenCache.containsKey(type)) {
			return mFlattenCache.get(type);
		}
		if (type instanceof BoogiePrimitiveType) {
			result = type;
		} else if (type instanceof BoogieConstructedType) {
			final BoogieConstructedType ctype = (BoogieConstructedType) type;
			final int numParams = ctype.getParameterCount();
			final BoogieType[] paramTypes = new BoogieType[numParams];
			for (int i = 0; i < paramTypes.length; i++) {
				paramTypes[i] = flattenType(ctype.getParameter(i));
				if (paramTypes[i] instanceof BoogieStructType) {
					final BoogieStructType st = (BoogieStructType) paramTypes[i];
					paramTypes[i] = createStructWrapperType(st);
				}
			}
			result = BoogieType.createConstructedType(ctype.getConstr(), paramTypes);
		} else if (type instanceof BoogieArrayType) {
			final BoogieArrayType at = (BoogieArrayType) type;
			final ArrayList<BoogieType> flattenedIndices = new ArrayList<>();
			for (int i = 0; i < at.getIndexCount(); i++) {
				final BoogieType flat = flattenType(at.getIndexType(i));
				if (flat instanceof BoogieStructType) {
					final BoogieStructType st = (BoogieStructType) flat;
					for (int j = 0; j < st.getFieldCount(); j++) {
						flattenedIndices.add(st.getFieldType(j));
					}
				} else {
					flattenedIndices.add(flat);
				}
			}
			final BoogieType[] indexTypes = flattenedIndices.toArray(new BoogieType[flattenedIndices.size()]);
			final BoogieType valueType = flattenType(at.getValueType());
			if (valueType instanceof BoogieStructType) {
				final BoogieStructType st = (BoogieStructType) valueType;
				final String[] names = st.getFieldIds();
				final BoogieType[] resultTypes = new BoogieType[names.length];
				for (int i = 0; i < names.length; i++) {
					resultTypes[i] =
							BoogieType.createArrayType(at.getNumPlaceholders(), indexTypes, st.getFieldType(i));
				}
				result = BoogieType.createStructType(names, resultTypes);
			} else {
				result = BoogieType.createArrayType(at.getNumPlaceholders(), indexTypes, valueType);
			}
		} else if (type instanceof BoogieStructType) {
			final BoogieStructType stype = (BoogieStructType) type;
			final ArrayList<String> allNames = new ArrayList<>();
			final ArrayList<BoogieType> allTypes = new ArrayList<>();
			for (int i = 0; i < stype.getFieldCount(); i++) {
				final String id = stype.getFieldIds()[i];
				final BoogieType bt = flattenType(stype.getFieldType(i));
				if (bt instanceof BoogieStructType) {
					final BoogieStructType st = (BoogieStructType) bt;
					for (int j = 0; j < st.getFieldCount(); j++) {
						allNames.add(id + DOT + st.getFieldIds()[j]);
						allTypes.add(st.getFieldType(j));
					}
				} else {
					allNames.add(id);
					allTypes.add(bt);
				}
			}
			final String[] names = allNames.toArray(new String[allNames.size()]);
			final BoogieType[] types = allTypes.toArray(new BoogieType[allTypes.size()]);
			result = BoogieType.createStructType(names, types);
		} else if (type instanceof BoogiePlaceholderType) {
			result = type;
		} else {
			throw new AssertionError("Unknown ASTType " + type);
		}
		mFlattenCache.put(type, result);
		return result;
	}

	@Override
	public void init(final ModelType modelType, final int currentModelIndex, final int numberOfModels) {
		// not needed
	}

	@Override
	public void finish() {
		// not needed
	}

	@Override
	public boolean performedChanges() {
		return true;
	}

	/**
	 * Process the boogie code.
	 */
	@Override
	public boolean process(final IElement root) {
		if (root instanceof Unit) {
			final Unit unit = (Unit) root;
			final ArrayDeque<Declaration> newDecls = new ArrayDeque<>();
			for (final Declaration d : unit.getDeclarations()) {
				final Declaration[] funcs = expandDeclaration(d);
				for (final Declaration newDecl : funcs) {
					mTranslator.addMapping(d, newDecl);
					newDecls.add(newDecl);
				}
			}
			for (final BoogieTypeConstructor tc : mStructTypes.values()) {
				final String[] typeParams = new String[tc.getParamCount()];
				for (int i = 0; i < typeParams.length; i++) {
					typeParams[i] = "$" + i;
				}
				final Declaration d = new TypeDeclaration(unit.getLocation(), new Attribute[0], tc.isFinite(),
						tc.getName(), typeParams);
				newDecls.addFirst(d);
			}
			unit.setDeclarations(newDecls.toArray(new Declaration[newDecls.size()]));
			return false;
		}
		return true;
	}

	/**
	 * Processes a list of varLists. This will expand declarations of structs into declarations for all fields in the
	 * struct. It is used for procedure and function parameters, and local and global variables.
	 *
	 * @param vls
	 *            the list of varlist to process.
	 * @return The expanded varlist.
	 */
	@Override
	protected VarList[] processVarLists(final VarList[] vls) {
		final ArrayList<VarList> flat = new ArrayList<>();
		for (final VarList vl : vls) {
			for (final VarList newVl : expandVarList(vl)) {
				flat.add(newVl);
				if (newVl != vl) {
					mTranslator.addMapping(vl, newVl);
				}
			}
		}
		if (flat.equals(Arrays.asList(vls))) {
			return vls;
		}
		return flat.toArray(new VarList[flat.size()]);
	}

	/**
	 * Expands a single var list. This will expand declarations of structs into declarations for all fields in the
	 * struct. If the declared variables have a struct type, it creates one declaration for every variable and every
	 * field in the struct.
	 *
	 * @param input
	 *            the var list to expand.
	 * @return The expanded varlist.
	 */
	private VarList[] expandVarList(final VarList input) {
		final IBoogieType oldType = input.getType().getBoogieType();
		final BoogieType bt = flattenType(oldType);

		if (bt instanceof BoogieStructType) {
			final BoogieStructType st = (BoogieStructType) bt;
			final VarList[] newVarList = new VarList[input.getIdentifiers().length * st.getFieldCount()];
			int i = 0;
			for (final String id : input.getIdentifiers()) {
				for (int j = 0; j < st.getFieldCount(); j++) {
					newVarList[i++] = new VarList(input.getLocation(), new String[] { id + DOT + st.getFieldIds()[j] },
							st.getFieldType(j).toASTType(input.getLocation()));
				}
			}
			return newVarList;
		}
		if (bt.equals(oldType)) {
			return new VarList[] { input };
		}
		return new VarList[] {
				new VarList(input.getLocation(), input.getIdentifiers(), bt.toASTType(input.getLocation())) };
	}

	/**
	 * Process expressions. Mainly this flattens the expression types, but it will also remove StructAccessExpression.
	 * It must only be called for expression that are not of a struct type after flattening.
	 *
	 * @param expr
	 *            the expression that should be processed.
	 * @returns the struct-free expression.
	 */
	@Override
	protected Expression processExpression(final Expression expr) {
		Expression newExpr = null;
		if (expr instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) expr;
			final Expression[] exprs = expandExpression(sae.getStruct());
			final BoogieStructType subType = (BoogieStructType) flattenType(sae.getStruct().getType());
			final String[] fields = subType.getFieldIds();
			assert (fields.length == exprs.length);
			for (int i = 0; i < fields.length; i++) {
				if (fields[i].equals(sae.getField())) {
					newExpr = exprs[i];
					ModelUtils.copyAnnotations(expr, newExpr);
					return newExpr;
				}
			}
			throw new RuntimeException("Field name not found in " + expr);
		}
		if (expr instanceof BinaryExpression) {
			final BinaryExpression binexpr = (BinaryExpression) expr;
			final BinaryExpression.Operator op = binexpr.getOperator();
			if (op == BinaryExpression.Operator.COMPEQ || op == BinaryExpression.Operator.COMPNEQ) {
				final Expression[] left = expandExpression(binexpr.getLeft());
				final Expression[] right = expandExpression(binexpr.getRight());
				assert (left.length == right.length && left.length > 0);
				final BinaryExpression.Operator andOp =
						op == BinaryExpression.Operator.COMPEQ ? BinaryExpression.Operator.LOGICAND
								: BinaryExpression.Operator.LOGICOR;
				int i = left.length - 1;
				Expression result = new BinaryExpression(expr.getLocation(), expr.getType(), op, left[i], right[i]);
				while (i-- > 0) {
					result = new BinaryExpression(expr.getLocation(), expr.getType(), andOp,
							new BinaryExpression(expr.getLocation(), expr.getType(), op, left[i], right[i]), result);
				}
				newExpr = result;
			}
		}
		if (newExpr == null) {
			final Expression result = super.processExpression(expr);
			result.setType(flattenType(expr.getType()));
			return result;
		}
		ModelUtils.copyAnnotations(expr, newExpr);
		return newExpr;
	}

	/**
	 * Expands the given expression in case the underlying type is a struct. In this case it returns an array of
	 * processed expression, one for each field. Otherwise this returns a singleton list with the processsed expression.
	 * The processed expressions are guaranteed to not contain any struct operations.
	 *
	 * @param e
	 *            the expression to expand.
	 * @return A list containing an expanded expression for every field in the flattened type of the original
	 *         expression.
	 */
	private Expression[] expandExpression(final Expression e) {
		if (e instanceof StringLiteral) {
			// StringLiteral cannot be expanded. StringLiteral do not have an
			// IType. Code below would crash, we return here.
			return new Expression[] { e };
		}
		if (e.getType() == null) {
			throw new IllegalArgumentException("The expression " + BoogiePrettyPrinter.print(e) + " has a null type!");
		}
		final BoogieType bt = flattenType(e.getType());
		if (!(bt instanceof BoogieStructType)) {
			// quick check, if process expression can be used.
			return new Expression[] { processExpression(e) };
		}

		final BoogieStructType st = (BoogieStructType) bt;
		if (e instanceof IdentifierExpression) {
			final IdentifierExpression ie = (IdentifierExpression) e;
			final String id = ie.getIdentifier();
			final Expression[] flattened = new Expression[st.getFieldCount()];
			for (int i = 0; i < flattened.length; i++) {
				final String ident = id + DOT + st.getFieldIds()[i];
				final IBoogieType type = st.getFieldType(i);
				flattened[i] = new IdentifierExpression(e.getLocation(), type, ident, ie.getDeclarationInformation());
			}
			return flattened;
		} else if (e instanceof ArrayAccessExpression) {
			final ArrayAccessExpression aae = (ArrayAccessExpression) e;
			final Expression[] arrays = expandExpression(aae.getArray());
			final Expression[] indices = processExpressions(aae.getIndices());
			final Expression[] result = new Expression[arrays.length];
			assert (st.getFieldCount() == result.length);
			for (int i = 0; i < result.length; i++) {
				final IBoogieType resultType = st.getFieldType(i);
				result[i] = new ArrayAccessExpression(aae.getLocation(), resultType, arrays[i], indices);
			}
			return result;
		} else if (e instanceof FunctionApplication) {
			final FunctionApplication app = (FunctionApplication) e;
			final Expression[] args = processExpressions(app.getArguments());
			final Expression[] result = new Expression[st.getFieldCount()];
			for (int i = 0; i < result.length; i++) {
				final String funcName = app.getIdentifier() + DOT + st.getFieldIds()[i];
				final IBoogieType resultType = st.getFieldType(i);
				result[i] = new FunctionApplication(app.getLocation(), resultType, funcName, args);
			}
			return result;
		} else if (e instanceof ArrayStoreExpression) {
			final ArrayStoreExpression ase = (ArrayStoreExpression) e;
			final Expression[] arrays = expandExpression(ase.getArray());
			final Expression[] indices = processExpressions(ase.getIndices());
			final Expression[] values = expandExpression(ase.getValue());
			final Expression[] result = new Expression[arrays.length];
			assert (st.getFieldCount() == result.length);
			for (int i = 0; i < result.length; i++) {
				final IBoogieType resultType = st.getFieldType(i);
				result[i] = new ArrayStoreExpression(ase.getLocation(), resultType, arrays[i], indices, values[i]);
			}
			return result;
		} else if (e instanceof StructConstructor) {
			return processExpressions(((StructConstructor) e).getFieldValues());
		} else if (e instanceof StructAccessExpression) {
			final StructAccessExpression sae = (StructAccessExpression) e;
			final Expression[] exprs = expandExpression(sae.getStruct());
			final BoogieStructType subType = (BoogieStructType) flattenType(sae.getStruct().getType());
			final String field = sae.getField();
			int start = -1, end = -1;
			for (int i = 0; i < subType.getFieldCount(); i++) {
				if (subType.getFieldIds()[i].startsWith(field + DOT)) {
					if (start == -1) {
						start = i;
					}
					end = i;
				}
			}
			if (start == -1) {
				throw new RuntimeException("Field name not found in " + e);
			}
			final Expression[] result = new Expression[end - start + 1];
			System.arraycopy(exprs, start, result, 0, end - start + 1);
			return result;
		} else if (e instanceof IfThenElseExpression) {
			final IfThenElseExpression ite = (IfThenElseExpression) e;
			final Expression[] thens = expandExpression(ite.getThenPart());
			final Expression[] elses = expandExpression(ite.getElsePart());
			assert (thens.length == elses.length);
			final Expression[] result = new Expression[thens.length];
			for (int i = 0; i < result.length; i++) {
				assert (thens[i].getType().equals(elses[i].getType()));
				result[i] = new IfThenElseExpression(ite.getLocation(), thens[i].getType(), ite.getCondition(),
						thens[i], elses[i]);
			}
			return result;
		} else if (e instanceof UnaryExpression) {
			/* this can only be an "old" expression */
			final UnaryExpression uexpr = (UnaryExpression) e;
			assert (uexpr.getOperator() == UnaryExpression.Operator.OLD);
			final Expression[] subExprs = expandExpression(uexpr.getExpr());
			final Expression[] result = new Expression[subExprs.length];
			for (int i = 0; i < result.length; i++) {
				result[i] =
						new UnaryExpression(e.getLocation(), subExprs[i].getType(), uexpr.getOperator(), subExprs[i]);
			}
			return result;
		} else {
			throw new AssertionError("Strange struct type expression " + e);
		}
	}

	/**
	 * Processes a list of expressions. This will expand expression that have a struct type to multiple expression, one
	 * for each field. This can thus be used to expand procedure and function arguments and the right hand sides of
	 * assignments.
	 *
	 * @param e
	 *            the expression list to process.
	 * @return A list containing the processed expression. This expands expression of struct type into multiple
	 *         expressions.
	 */
	@Override
	protected Expression[] processExpressions(final Expression[] exprs) {
		final ArrayList<Expression> flat = new ArrayList<>();
		for (final Expression e : exprs) {
			flat.addAll(Arrays.asList(expandExpression(e)));
		}
		return flat.toArray(new Expression[flat.size()]);
	}

	/**
	 * Processes a single left hand side. This must only be called for left hand sides that are not of struct type.
	 *
	 * @param lhs
	 *            the left hand sides to process.
	 * @return The processed lhs.
	 */
	@Override
	protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
		if (lhs instanceof StructLHS) {
			final StructLHS slhs = (StructLHS) lhs;
			final LeftHandSide[] allFields = expandLeftHandSide(slhs.getStruct());
			final BoogieStructType st = (BoogieStructType) flattenType(slhs.getStruct().getType());
			for (int i = 0; i < st.getFieldCount(); i++) {
				if (st.getFieldIds()[i].equals(slhs.getField())) {
					final LeftHandSide newLhs = allFields[i];
					ModelUtils.copyAnnotations(lhs, newLhs);
					return newLhs;
				}
			}
			throw new RuntimeException("Field name not found in " + lhs);
		}
		final LeftHandSide result = super.processLeftHandSide(lhs);
		result.setType(flattenType(lhs.getType()));
		return result;
	}

	/**
	 * Processes a single left hand side and expands it. This will expand an lhs if it has struct type into one for each
	 * field.
	 *
	 * @param lhs
	 *            the left hand sides to process.
	 * @return The expanded lhs.
	 */
	private LeftHandSide[] expandLeftHandSide(final LeftHandSide lhs) {
		if (lhs.getType() == null) {
			throw new IllegalArgumentException("type of " + lhs.toString() + " is null");
		}
		final BoogieType bt = flattenType(lhs.getType());
		if (!(bt instanceof BoogieStructType)) {
			// quick check, if process expression can be used.
			return new LeftHandSide[] { processLeftHandSide(lhs) };
		}
		final BoogieStructType st = (BoogieStructType) bt;

		if (lhs instanceof VariableLHS) {
			final VariableLHS vlhs = (VariableLHS) lhs;
			final String id = vlhs.getIdentifier();
			final VariableLHS[] flattened = new VariableLHS[st.getFieldCount()];
			for (int i = 0; i < flattened.length; i++) {
				final String ident = id + DOT + st.getFieldIds()[i];
				final IBoogieType type = st.getFieldType(i);
				flattened[i] = new VariableLHS(lhs.getLocation(), type, ident, vlhs.getDeclarationInformation());
			}
			return flattened;
		} else if (lhs instanceof ArrayLHS) {
			final ArrayLHS alhs = (ArrayLHS) lhs;
			final LeftHandSide[] arrays = expandLeftHandSide(alhs.getArray());
			final Expression[] indices = processExpressions(alhs.getIndices());
			final LeftHandSide[] result = new LeftHandSide[arrays.length];
			for (int i = 0; i < result.length; i++) {
				final IBoogieType resultType = st.getFieldType(i);
				result[i] = new ArrayLHS(alhs.getLocation(), resultType, arrays[i], indices);
			}
			return result;
		} else if (lhs instanceof StructLHS) {
			final StructLHS slhs = (StructLHS) lhs;
			final LeftHandSide[] allFields = expandLeftHandSide(slhs.getStruct());
			final BoogieStructType subType = (BoogieStructType) flattenType(slhs.getStruct().getType());
			assert (subType.getFieldCount() == allFields.length);
			int start = -1, end = -1;
			for (int i = 0; i < subType.getFieldCount(); i++) {
				if (subType.getFieldIds()[i].startsWith(slhs.getField() + DOT)) {
					if (start == -1) {
						start = i;
					}
					end = i;
				}
			}
			if (start == -1) {
				throw new RuntimeException("Field name not found in " + lhs);
			}
			final LeftHandSide[] result = new LeftHandSide[end - start + 1];
			System.arraycopy(allFields, start, result, 0, end - start + 1);
			return result;
		} else {
			throw new AssertionError("Strange LHS " + lhs);
		}
	}

	/**
	 * Processes a list of left hand sides. This will expand lhs that have a struct type to multiple lhs, one for each
	 * field. This can thus be used to expand the lhs of an assignment of procedure call or the havoc or modified list.
	 *
	 * @param lhss
	 *            the list of left hand sides to process.
	 * @return A list containing the processed lhs.
	 */
	@Override
	protected LeftHandSide[] processLeftHandSides(final LeftHandSide[] lhss) {
		final ArrayList<LeftHandSide> flat = new ArrayList<>();
		for (final LeftHandSide e : lhss) {
			flat.addAll(Arrays.asList(expandLeftHandSide(e)));
		}
		return flat.toArray(new LeftHandSide[flat.size()]);
	}

	/**
	 * Expand function and constant declarations. For a function declaration:
	 * <ul>
	 * <li>iff return value is of struct type: declare a function for each struct field recursively. <br />
	 * E.g.:<br />
	 *
	 * <pre>
	 * <code>function f() returns (v:{f1:int, f2:bool});</code>
	 * </pre>
	 *
	 * to:<br />
	 *
	 * <pre>
	 * <code>function f.f1() returns (v:int);<br />
	 * function f.f2() returns (v:bool);</code>
	 * </pre>
	 *
	 * </li>
	 * <li>for each param p : if p is of struct type: expand to multiple in params</li>
	 * <li>otherwise: return function declaration as is.</li>
	 * <ul>
	 *
	 * @param decl
	 *            the declaration to expand.
	 * @return new declarations.
	 */
	private Declaration[] expandDeclaration(final Declaration decl) {
		if (decl instanceof FunctionDeclaration) {
			final FunctionDeclaration funDecl = (FunctionDeclaration) decl;
			final IBoogieType retType = funDecl.getOutParam().getType().getBoogieType();
			final BoogieType bt = flattenType(retType);
			if (!(bt instanceof BoogieStructType)) {
				// this checks if there are illegal { : expand_struct ""} attributes
				processExpandStructAttribute(funDecl, 0, null);
				// quick check, if processDeclaration can be used.
				return new Declaration[] { processDeclaration(funDecl) };
			}
			final BoogieStructType st = (BoogieStructType) bt;
			final Declaration[] newDecls = new Declaration[st.getFieldCount()];
			Expression[] bodies;
			if (funDecl.getBody() == null) {
				bodies = new Expression[st.getFieldCount()];
			} else {
				bodies = expandExpression(funDecl.getBody());
			}
			final VarList[] newInParams = processVarLists(funDecl.getInParams());
			final Attribute[][] newAttribs = processExpandStructAttribute(funDecl, st.getFieldCount(), st);

			for (int i = 0; i < newDecls.length; i++) {
				final ILocation loc = funDecl.getOutParam().getLocation();
				final VarList newOutParam =
						new VarList(loc, funDecl.getOutParam().getIdentifiers(), st.getFieldType(i).toASTType(loc));
				assert newAttribs[i] != null;
				newDecls[i] = new FunctionDeclaration(funDecl.getLocation(), newAttribs[i],
						funDecl.getIdentifier() + DOT + st.getFieldIds()[i], funDecl.getTypeParams(), newInParams,
						newOutParam, bodies[i]);
			}
			return newDecls;
		} else if (decl instanceof ConstDeclaration) {
			final ConstDeclaration cdecl = (ConstDeclaration) decl;
			final VarList varList = cdecl.getVarList();
			final VarList[] newVarList = expandVarList(varList);
			if (newVarList.length == 1 && newVarList[0] == varList) {
				return new Declaration[] { decl };
			}

			final Declaration[] newDecls = new Declaration[newVarList.length];
			for (int i = 0; i < newDecls.length; i++) {
				newDecls[i] = new ConstDeclaration(cdecl.getLocation(), cdecl.getAttributes(), cdecl.isUnique(),
						newVarList[i], cdecl.getParentInfo(), cdecl.isComplete());
			}
			return newDecls;
		} else if (decl instanceof TypeDeclaration) {
			final TypeDeclaration td = (TypeDeclaration) decl;
			Declaration result = td;
			if (td.getSynonym() != null) {
				final BoogieType bt = flattenType(td.getSynonym().getBoogieType());
				if (bt instanceof BoogieStructType) {
					return new Declaration[0];
				}
				if (!bt.equals(td.getSynonym().getBoogieType())) {
					result = new TypeDeclaration(td.getLocation(), td.getAttributes(), td.isFinite(),
							td.getIdentifier(), td.getTypeParams(), bt.toASTType(td.getLocation()));
				}
			}
			return new Declaration[] { result };
		} else {
			return new Declaration[] { processDeclaration(decl) };
		}
	}

	/**
	 * Consume {:expand-struct "id"} attributes of a function by splitting the original attribute array into new ones
	 * along the occurrences of {:expand-struct "id"} attributes.
	 *
	 * @param funDecl
	 *            the declaration of the function
	 * @param fieldCount
	 *            the number of fields the return type of the function has
	 * @param st
	 *            The flattened return type of the function
	 * @return A splitting of {@link Attribute}s
	 */
	private Attribute[][] processExpandStructAttribute(final FunctionDeclaration funDecl, final int fieldCount,
			final BoogieStructType st) {
		final Attribute[] attribs = funDecl.getAttributes();
		if (fieldCount < 0) {
			throw new IllegalArgumentException("negative field count");
		}
		if (attribs == null) {
			final Attribute[][] rtr = new Attribute[fieldCount][0];
			for (int i = 0; i < fieldCount; ++i) {
				rtr[i] = null;
			}
			return rtr;
		}
		if (attribs.length == 0) {
			final Attribute[][] rtr = new Attribute[fieldCount][0];
			for (int i = 0; i < fieldCount; ++i) {
				rtr[i] = new Attribute[0];
			}
			return rtr;
		}
		if (fieldCount == 0) {
			if (Arrays.stream(attribs).filter(a -> a instanceof NamedAttribute).map(a -> ((NamedAttribute) a).getName())
					.anyMatch(a -> a.equals(ATTRIBUTE_EXPAND_STRUCT))) {
				throw new IllegalExpandStructUsageException(funDecl.getIdentifier() + " has " + ATTRIBUTE_EXPAND_STRUCT
						+ " attribute but no struct return type");
			}
			final Attribute[][] rtr = new Attribute[0][];
			rtr[0] = funDecl.getAttributes();
			return rtr;
		}

		final Attribute[][] rtr = new Attribute[fieldCount][];
		int lastIdx = -1;
		int rtrIdx = 0;
		for (int i = 0; i < attribs.length; ++i) {
			if (!(attribs[i] instanceof NamedAttribute)) {
				continue;
			}
			final NamedAttribute namedAttrib = (NamedAttribute) attribs[i];
			if (!ATTRIBUTE_EXPAND_STRUCT.equals(namedAttrib.getName())) {
				continue;
			}
			if (lastIdx != -1) {
				fillNextAttributeSegment(funDecl, st, attribs, rtr, lastIdx, rtrIdx, i);
				rtrIdx++;

			} else {
				if (lastIdx == -1 && i != 0) {
					throw new IllegalExpandStructUsageException(funDecl.getIdentifier() + " " + ATTRIBUTE_EXPAND_STRUCT
							+ " attribute is not the first attribute; you will loose attributes");
				}
			}
			lastIdx = i;
		}
		fillNextAttributeSegment(funDecl, st, attribs, rtr, lastIdx, rtrIdx, attribs.length);
		rtrIdx++;

		for (; rtrIdx < rtr.length; ++rtrIdx) {
			rtr[rtrIdx] = new Attribute[0];
		}
		return rtr;
	}

	private void fillNextAttributeSegment(final FunctionDeclaration funDecl, final BoogieStructType st,
			final Attribute[] attribs, final Attribute[][] rtr, final int lastIdx, final int rtrIdx, final int i) {
		if (rtrIdx >= rtr.length) {
			throw new IllegalExpandStructUsageException(funDecl.getIdentifier() + " has too many "
					+ ATTRIBUTE_EXPAND_STRUCT + " attributes for its return type");
		}
		if (lastIdx == -1) {
			throw new IllegalExpandStructUsageException(funDecl.getIdentifier() + " has no " + ATTRIBUTE_EXPAND_STRUCT
					+ " attribute but struct return type");
		}
		// copy all attributes after lastIdx and before i into a new array and save it at rtr[rtrIdx]
		final int newLength = i - lastIdx - 1;
		final Attribute[] dest = new Attribute[newLength];
		System.arraycopy(attribs, lastIdx + 1, dest, 0, newLength);
		rtr[rtrIdx] = dest;

		final String currentFieldId = st.getFieldIds()[rtrIdx];
		final Expression expandStructArg = ((NamedAttribute) attribs[lastIdx]).getValues()[0];
		if (!(expandStructArg instanceof StringLiteral)) {
			throw new IllegalExpandStructUsageException(funDecl.getIdentifier() + " has " + ATTRIBUTE_EXPAND_STRUCT
					+ " attribute but wrong attribute type");
		}
		final String expectedFieldName = ((StringLiteral) expandStructArg).getValue();
		if (!currentFieldId.equals(expectedFieldName)) {
			throw new IllegalExpandStructUsageException(funDecl.getIdentifier() + " has " + ATTRIBUTE_EXPAND_STRUCT
					+ " attribute but field names and " + ATTRIBUTE_EXPAND_STRUCT + " names do not match: "
					+ currentFieldId + " vs. " + expectedFieldName);
		}
	}

	@Override
	protected Statement processStatement(final Statement statement) {
		final Statement rtr = super.processStatement(statement);
		if (rtr != statement) {
			mTranslator.addMapping(statement, rtr);
		}
		return rtr;
	}

	/**
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 */
	private static final class IllegalExpandStructUsageException extends RuntimeException {

		private static final long serialVersionUID = 1L;

		public IllegalExpandStructUsageException(final String msg) {
			super(msg);
		}

	}
}
