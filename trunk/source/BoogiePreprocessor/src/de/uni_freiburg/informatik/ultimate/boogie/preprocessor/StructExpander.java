/**
 * Class that handles expanding of structs into normal variables.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructType;
import de.uni_freiburg.informatik.ultimate.boogie.type.TypeConstructor;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfThenElseExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.wrapper.WrapperNode;

/**
 * This class removes our Boogie syntax extension of structs and
 * creates a plain Boogie code without the struct extension.
 * 
 * The extensions for struct we support are:
 * New ASTType:
 * <pre>StructType ::= fields : VarList[]<pre>
 * 
 * New LeftHandSide:
 * <pre>StructLHS ::=  struct: LeftHandSide, field:String</pre>
 * 
 * New Expressions:
 * <pre>StructAccessExpression ::=  struct : Expression, field:String
 * StructConstructor ::= fieldIdentifiers : String[], fieldValues : Expression[]</pre>
 * Also, IdentifierExpression and VariableLHS can refer to struct
 * typed variables.  And functions can take struct typed parameters
 * and return struct typed values.
 * 
 * The semantic type of a boogie.ast.StructType is represented by 
 * boogie.type.StructType. This contains an array of fieldNames (String) 
 * and an array of fieldTypes (BoogieType) of the same length.
 * Two struct types are identical if they declare the same names of the 
 * same types in the same order.  The field types can also be struct typed
 * and one can build arrays over structs and structs over arrays.
 * 
 * This class gets rids of structs by flattening them and replacing them
 * by the finite list of values.
 * 
 * If a struct type is used as index type of an array, it is replaced
 * by a multidimensional array, one index type for every element in the
 * struct, forgetting the names of the fields.
 * E.g., <code>[{a:int,b:real]int</code> is transformed to
 * <code>[int,real]int</code>
 * If a struct type is used as element type of an array, the struct is
 * pulled to the outside, hence it is a struct of arrays, all with the
 * same index type and the element type of the corresponding field.
 * E.g., <code>[int]{a:int,b:real}</code> is transformed to
 * <code>{a:[int]int, b:[int]real}</code>
 * A struct type in a struct is flattened and the field names are combined
 * with DOT. e.g. the type <code>{ a : int, b: { x:int, y:int}}</code>
 * is flattened to <code>{ a: int, b.x : int, b.y : int}</code>.
 * After these transformation a type can contain a struct type only on
 * the outside. 
 *
 * For every variable declaration occuring in the BoogieAST with a
 * struct type, we create one variable for each field, e.g.
 * <code>var x,y: {a:int,b:real}, z:real;<code>
 * is transformed to
 * <code>var x.a:int, x.b:real, y.a:int, y.b:real, z:real</code>.
 * This also includes the variable lists used for input parameters 
 * in function and procedure declarations and for output parameters
 * in procedures.  
 * 
 * A function returning a struct is replaced by several functions, one
 * for each field.  The name also uses the DOT, e.g.,
 * <code>function f () : {a:int,b:real}<code>
 *  is expanded to
 * <code>function f.a () : int; function f.b():real}<code>
 * 
 * In assignments and procedure calls (which are also assignments), the
 * left-hand-sides that are of struct type are expanded to a list of
 * left-hand-sides, one for each field.
 * An expression of a struct type is replaced by a list of expressions
 * one for each field.
 * 
 * The expansion of expression of struct types works as follows:
 * An IdentifierExpression is expanded to one IdentifierExpression for
 * every field, matching the way the variable declaration is expanded.
 * An FunctionApplication is expanded into a list of FunctionApplication
 * one for each field.  The function parameters are just duplicated.
 * An array access is expanded recursively, e.g., if <code>expr<code> 
 * expands to <code>e1,...,en<code>, <code>expr[i]<code> expands to
 * <code>e1[i],...,en[i]<code>
 * 
 * 
 * 
 * @author Markus Lindenmann, Jochen Hoenicke
 * @date 26.08.2012
 */
public class StructExpander extends BoogieTransformer implements
        IUnmanagedObserver {
    /**
     * String holding a period / dot.
     */
    private static final String DOT = ".";
    
    /**
     * The cache used by flattenType to prevent repeated work.
     */
    private HashMap<BoogieType, BoogieType> m_FlattenCache;
    /**
     * This map remembers the created struct types.
     * For named type parameters that have struct type, we create a new
     * pseudo type struct~f1~f2, where f1,f2 are the names of the field
     * and that takes the types of f1 and f2 as parameters.  This is used
     * to instantiate these type parameters.
     * E.g. the type <code>Field {a:int, b:real}</code> is flattened
     * to <code>Field (struct~a~b int real)</code>.  We need to remember
     * to add the type declaration
     * <pre>type struct~a~b $0 $1;</pre>
     * which is remembered in this map.
     */
    private HashMap<String, TypeConstructor> m_StructTypes;

    /**
     * Create a new struct wrapper type and register the corresponding
     * type constructor, unless that is already present.  The input type
     * must already be flattened, i.e., the field types do not contain
     * any structs.
     * @param st the struct type for which a wrapper is created.
     * @returns a new constructed type for this struct type.
     */
    private BoogieType createStructWrapperType(StructType st) {
		StringBuilder sb = new StringBuilder();
		sb.append("struct");
		for (String f : st.getFieldIds())
			sb.append('~').append(f);
		String name = sb.toString();
		TypeConstructor tc = m_StructTypes.get(name);
		if (tc == null) {
			int[] paramOrder = new int[st.getFieldCount()];
			for (int i= 0; i < paramOrder.length; i++)
				paramOrder[i] = i;
			tc = new TypeConstructor(name, st.isFinite(), st.getFieldCount(), paramOrder);
			m_StructTypes.put(name, tc);
		}
		BoogieType[] types = new BoogieType[st.getFieldCount()];
		for (int i = 0; i< types.length; i++)
			types[i] = st.getFieldType(i);
		return BoogieType.createConstructedType(tc, types);
    }
    
    /**
     * Convert a type to a flattened type, where there is a single 
     * struct type at the outside.  arrays of structs are converted
     * to structs of arrays and nested structs are flattened.
     * We work on BoogieType and use getUnderlyingType() so that we 
     * do not need to handle type aliases. 
     * @param itype  the type that should be flattened.  This must
     *   be a BoogieType, but we want to avoid casts everywhere.
     * @return the flattened type as BoogieType.
     */
    private BoogieType flattenType(IType itype) {
    	BoogieType result;
    	BoogieType type = ((BoogieType)itype).getUnderlyingType();
    	if (m_FlattenCache.containsKey(type))
    		return m_FlattenCache.get(type);
    	if (type instanceof PrimitiveType) {
    		result = type;
    	} else if (type instanceof ConstructedType) {
    		ConstructedType ctype = (ConstructedType) type;
    		int numParams = ctype.getParameterCount();
    		BoogieType[] paramTypes = new BoogieType[numParams];
    		for (int i = 0; i < paramTypes.length; i++) {
    			paramTypes[i] = flattenType(ctype.getParameter(i));
    			if (paramTypes[i] instanceof StructType) {
    				StructType st = (StructType) paramTypes[i];
    				paramTypes[i] = createStructWrapperType(st);
    			}
    		}
    		result = BoogieType.createConstructedType(ctype.getConstr(), paramTypes);
    	} else if (type instanceof ArrayType) {
    		ArrayType at = (ArrayType) type;
        	ArrayList<BoogieType> flattenedIndices = new ArrayList<BoogieType>();
    		for (int i = 0; i < at.getIndexCount(); i++) {
        		BoogieType flat = flattenType(at.getIndexType(i));
        		if (flat instanceof StructType) {
        			StructType st = (StructType) flat;
        			for (int j = 0; j < st.getFieldCount(); j++)
        				flattenedIndices.add(st.getFieldType(j));
        		} else {
        			flattenedIndices.add(flat);
        		}
        	}
    		BoogieType[] indexTypes = flattenedIndices.toArray
    				(new BoogieType[flattenedIndices.size()]);
    		BoogieType valueType = at.getValueType();
    		if (valueType instanceof StructType) {
    			StructType st = (StructType) valueType;
    			String[] names = st.getFieldIds();
    			BoogieType[] resultTypes = new BoogieType[names.length];
    			for (int i = 0; i < names.length; i++) {
    				resultTypes[i] = BoogieType.createArrayType
    						(at.getNumPlaceholders(), 
    						indexTypes, st.getFieldType(i));
    			}
    			result = BoogieType.createStructType(names, resultTypes);
    		} else {
    			result = BoogieType.createArrayType(at.getNumPlaceholders(), 
    					indexTypes, valueType);
    		}
    	} else if (type instanceof StructType) {
    		StructType stype = (StructType) type;
    		ArrayList<String> allNames = new ArrayList<String>();
    		ArrayList<BoogieType> allTypes = new ArrayList<BoogieType>();
    		for (int i = 0; i < stype.getFieldCount(); i++) {
    			String id = stype.getFieldIds()[i];
    			BoogieType bt = flattenType(stype.getFieldType(i));
    			if (bt instanceof StructType) {
    				StructType st = (StructType) bt;
    				for (int j = 0; j < st.getFieldCount(); j++) {
    					allNames.add(id + DOT + st.getFieldIds()[j]);
    					allTypes.add(st.getFieldType(j));
    				}
    			} else {
    				allNames.add(id);
    				allTypes.add(bt);
    			}
    		}
    		String[] names = allNames.toArray(new String[allNames.size()]);
    		BoogieType[] types = allTypes.toArray(new BoogieType[allTypes.size()]);
    		result = BoogieType.createStructType(names, types);
    	} else {
    		throw new AssertionError("Unknown ASTType "+type);
    	}
    	m_FlattenCache.put(type, result);
    	return result;
    }

    @Override
    public void init() {
    	this.m_FlattenCache = new HashMap<BoogieType, BoogieType>();
    	this.m_StructTypes = new HashMap<String, TypeConstructor>();
    }

    @Override
    public void finish() {
        this.m_FlattenCache = null;
        this.m_StructTypes = null;
    }

    @Override
    public WalkerOptions getWalkerOptions() {
        return null;
    }

    @Override
    public boolean performedChanges() {
        return true;
    }

    /**
     * Process the boogie code.
     */
    @Override
    public boolean process(IElement root) {
        if (root instanceof WrapperNode) {
            Unit unit = (Unit) ((WrapperNode) root).getBacking();
            ArrayDeque<Declaration> newDecls = new ArrayDeque<Declaration>();
            for (Declaration d : unit.getDeclarations()) {
                if (d instanceof FunctionDeclaration) {
                    Declaration[] funcs = expandFunctionDeclaration((FunctionDeclaration) d);
                    newDecls.addAll(Arrays.asList(funcs));
                } else {
                    Declaration decl = processDeclaration(d);
                    if (decl != null)
                        newDecls.add(decl);
                }
            }
            for (TypeConstructor tc : m_StructTypes.values()) {
            	String[] typeParams = new String[tc.getParamCount()];
            	for (int i = 0; i < typeParams.length; i++) 
            		typeParams[i] = "$"+i;
            	Declaration d = new TypeDeclaration(unit.getLocation(), 
            		new Attribute[0], tc.isFinite(), tc.getName(), typeParams);
            	newDecls.addFirst(d);
            }
            unit.setDeclarations(newDecls.toArray(new Declaration[0]));
            return false;
        }
        return true;
    }

    /**
     * Process declarations.  This will just remove type declarations
     * that are no longer valid since they declare struct types.
     * @param d the declaration to process.
     * @returns the same declaration, or null if it should be removed.
     */
    @Override
    protected Declaration processDeclaration(final Declaration d) {
        if (d instanceof TypeDeclaration) {
        	TypeDeclaration td = (TypeDeclaration) d;
        	if (td.getSynonym() != null) {
        		BoogieType bt = flattenType(td.getSynonym().getBoogieType());
        		if (bt instanceof StructType)
        			return null;
        		if (bt.equals(td.getSynonym().getBoogieType()))
        			return td;
        		return new TypeDeclaration(
        				td.getLocation(), td.getAttributes(), td.isFinite(), 
       					td.getIdentifier(), td.getTypeParams(), 
       					bt.toASTType(td.getLocation()));
        	}
        }
        return super.processDeclaration(d);
    }


    /**
     * Processes a list of varLists.  This will expand declarations of
     * structs into declarations for all fields in the struct.  It is
     * used for procedure and function parameters, and local and global 
     * variables. 
     * 
     * @param vls the list of varlist to process.
     * @return The expanded varlist. 
     */
    @Override
    protected VarList[] processVarLists(VarList[] vls) {
    	ArrayList<VarList> flat = new ArrayList<VarList>();
    	for (VarList vl : vls) {
    		flat.addAll(Arrays.asList(expandVarList(vl)));
    	}
    	if (flat.equals(Arrays.asList(vls)))
    		return vls;
    	return flat.toArray(new VarList[flat.size()]);
    }

    /**
     * Expands a single var list.  This will expand declarations of
     * structs into declarations for all fields in the struct.
     * If the declared variables have a struct type, it creates one
     * declaration for every variable and every field in the struct.  
     * 
     * @param input the var list to expand.
     * @return The expanded varlist. 
     */
    private VarList[] expandVarList(VarList input) {
    	IType oldType = input.getType().getBoogieType();
    	BoogieType bt = flattenType(oldType);
    	
    	if (bt instanceof StructType) {
    		StructType st = (StructType) bt;
    		VarList[] newVarList = 
    				new VarList[input.getIdentifiers().length * st.getFieldCount()];
    		int i = 0;
    		for (String id: input.getIdentifiers()) {
    			for (int j = 0; j < st.getFieldCount(); j++) {
    				newVarList[i++] = new VarList(input.getLocation(),
    					new String[] { id + DOT + st.getFieldIds()[j] }, 
    					st.getFieldType(j).toASTType(input.getLocation()));
    			}
    		}
        	return newVarList;
    	} else {
        	if (bt.equals(oldType))
        		return new VarList[] {input};
    		return new VarList[] {
    			new VarList(input.getLocation(), input.getIdentifiers(),
    					bt.toASTType(input.getLocation()))
    		};
    	}
    }

    /**
     * Process expressions.  Mainly this flattens the expression types, but
     * it will also remove StructAccessExpression.  It must only be called
     * for expression that are not of a struct type after flattening.
     * @param expr the expression that should be processed.
     * @returns the struct-free expression.
     */
    @Override
    protected Expression processExpression(final Expression expr) {
        if (expr instanceof StructAccessExpression) {
        	StructAccessExpression sae = (StructAccessExpression) expr;
        	Expression[] exprs = expandExpression(sae.getStruct());
        	StructType subType = (StructType) flattenType(sae.getStruct().getType());
        	String[] fields = subType.getFieldIds();
        	assert (fields.length == exprs.length);
        	for (int i = 0; i < fields.length; i++) {
        		if (fields[i].equals(sae.getField()))
        			return exprs[i];
        	}
        	throw new RuntimeException("Field name not found in "+expr);
        }
        if (expr instanceof BinaryExpression) {
        	BinaryExpression binexpr = (BinaryExpression) expr;
        	BinaryExpression.Operator op = binexpr.getOperator(); 
        	if (op == BinaryExpression.Operator.COMPEQ
        		|| op == BinaryExpression.Operator.COMPNEQ) {
        		Expression[] left = expandExpression(binexpr.getLeft());
        		Expression[] right = expandExpression(binexpr.getRight());
        		assert(left.length == right.length && left.length > 0);
        		BinaryExpression.Operator andOp =
        				op == BinaryExpression.Operator.COMPEQ
        						? BinaryExpression.Operator.LOGICAND
        						: BinaryExpression.Operator.LOGICOR;
        		int i = left.length - 1;
        		Expression result = 
        			new BinaryExpression(expr.getLocation(), expr.getType(), op, left[i], right[i]);
        		while (i-- > 0) {
        			result = new BinaryExpression(expr.getLocation(), expr.getType(), andOp,
        				new BinaryExpression(expr.getLocation(), expr.getType(), op, left[i], right[i]),
        				result);
        		}
        		return result;
        	}
        }
        Expression result = super.processExpression(expr);
        result.setType(flattenType(expr.getType()));
        return result;
    }
    /**
     * Expands the given expression in case the underlying type is a struct.
     * In this case it returns an array of processed expression, one for 
     * each field.  Otherwise this returns a singleton list with the 
     * processsed expression.  The processed expressions are guaranteed to 
     * not contain any struct operations.
     * 
     * @param e  the expression to expand.
     * @return A list containing an expanded expression for every field
     *   in the flattened type of the original expression.
     */
    private Expression[] expandExpression(Expression e) {
    	BoogieType bt = flattenType(e.getType());
    	if (! (bt instanceof StructType)) {
    		// quick check, if process expression can be used.
    		return new Expression[] { processExpression(e) };
    	}

    	StructType st = (StructType) bt;
        if (e instanceof IdentifierExpression) {
        	String id = ((IdentifierExpression) e).getIdentifier();
    		Expression[] flattened = new Expression[st.getFieldCount()];
    		for (int i = 0; i < flattened.length; i++) {
    			String ident = id + DOT + st.getFieldIds()[i];
    			IType type = st.getFieldType(i);
    			flattened[i] =
    					new IdentifierExpression(e.getLocation(), type, ident);
    		}
    		return flattened;
        } else if (e instanceof ArrayAccessExpression) {
            ArrayAccessExpression aae = (ArrayAccessExpression) e;
        	Expression[] arrays = expandExpression(aae.getArray());
        	Expression[] indices = processExpressions(aae.getIndices());
        	Expression[] result = new Expression[arrays.length];
        	assert (st.getFieldCount() == result.length);
        	for (int i = 0; i < result.length; i++) {
        		IType resultType = st.getFieldType(i); 
       			result[i] = new ArrayAccessExpression
       				(aae.getLocation(), resultType, arrays[i], indices);
        	}
        	return result;
        } else if (e instanceof FunctionApplication) {
        	FunctionApplication app = (FunctionApplication) e;
        	Expression[] args = processExpressions(app.getArguments());
        	Expression[] result = new Expression[st.getFieldCount()];
        	for (int i = 0; i < result.length; i++) {
        		String funcName = app.getIdentifier() + DOT + st.getFieldIds()[i]; 
        		IType resultType = st.getFieldType(i);
        		result[i] = new FunctionApplication
        				(app.getLocation(), resultType, funcName, args);
        	}
        	return result;
        } else if (e instanceof ArrayStoreExpression) {
            ArrayStoreExpression ase = (ArrayStoreExpression) e;
        	Expression[] arrays = expandExpression(ase.getArray());
        	Expression[] indices = processExpressions(ase.getIndices());
        	Expression[] values = expandExpression(ase.getValue());
        	Expression[] result = new Expression[arrays.length];
        	assert (st.getFieldCount() == result.length);
        	for (int i = 0; i < result.length; i++) {
        		IType resultType = st.getFieldType(i);
        		result[i] = new ArrayStoreExpression
       				(ase.getLocation(), resultType, 
       				arrays[i], indices, values[i]);
        	}
        	return result;
        } else if (e instanceof StructConstructor) {
        	return processExpressions(((StructConstructor) e).getFieldValues());
        } else if (e instanceof StructAccessExpression) {
        	StructAccessExpression sae = (StructAccessExpression) e;
        	Expression[] exprs = expandExpression(sae.getStruct());
        	StructType subType = (StructType) flattenType(sae.getStruct().getType());
        	String field = sae.getField();
        	int start = -1, end = -1;
        	for (int i = 0; i < subType.getFieldCount(); i++) {
        		if (subType.getFieldIds()[i].startsWith(field+DOT)) {
        			if (start == -1)
        				start = i;
        			end = i;
        		}
        	}
        	if (start == -1)
        		throw new RuntimeException("Field name not found in "+e);
        	Expression[] result = new Expression[end-start+1];
        	System.arraycopy(exprs, start, result, 0, end - start + 1);
        	return result;
        } else if (e instanceof IfThenElseExpression) {
        	IfThenElseExpression ite = (IfThenElseExpression) e;
        	Expression[] thens = expandExpression(ite.getThenPart());
        	Expression[] elses = expandExpression(ite.getElsePart());
        	assert (thens.length == elses.length);
        	Expression[] result = new Expression[thens.length];
        	for (int i = 0; i < result.length; i++) {
        		assert (thens[i].getType().equals(elses[i].getType()));
        		result[i] = new IfThenElseExpression
        			(ite.getLocation(), thens[i].getType(),
        			 ite.getCondition(), thens[i], elses[i]);
        	}
        	return result;
        } else {
        	throw new AssertionError("Strange struct type expression "+e);
        }
    }

    /**
     * Processes a list of expressions.  This will expand expression that
     * have a struct type to multiple expression, one for each field.  This
     * can thus be used to expand procedure and function arguments and the 
     * right hand sides of assignments.
     * 
     * @param e  the expression list to process.
     * @return A list containing the processed expression.  This expands
     *   expression of struct type into multiple expressions. 
     */
    @Override
    protected Expression[] processExpressions(Expression[] exprs) {
    	ArrayList<Expression> flat = new ArrayList<Expression>();
    	for (Expression e : exprs) {
    		flat.addAll(Arrays.asList(expandExpression(e)));
    	}
    	return flat.toArray(new Expression[flat.size()]);
    }

    /**
     * Processes a single left hand side.  This must only be called
     * for left hand sides that are not of struct type.  
     * 
     * @param lhs  the left hand sides to process.
     * @return The processed lhs. 
     */
    @Override
    protected LeftHandSide processLeftHandSide(LeftHandSide lhs) {
    	if (lhs instanceof StructLHS) {
    		StructLHS slhs = (StructLHS) lhs;
    		LeftHandSide[] allFields = expandLeftHandSide(slhs.getStruct());
    		StructType st = (StructType) flattenType(slhs.getStruct().getType());
    		for (int i = 0; i < st.getFieldCount(); i++) {
    			if (st.getFieldIds()[i].equals(slhs.getField()))
    				return allFields[i];
    		}
    		throw new RuntimeException("Field name not found in "+lhs);
    	}
    	LeftHandSide result = super.processLeftHandSide(lhs);
    	result.setType(flattenType(lhs.getType()));
    	return result;
    }
    
    /**
     * Processes a single left hand side and expands it.  This will
     * expand an lhs if it has struct type into one for each field.
     * 
     * @param lhs  the left hand sides to process.
     * @return The expanded lhs. 
     */
    private LeftHandSide[] expandLeftHandSide(LeftHandSide lhs) {
    	BoogieType bt = flattenType(lhs.getType());
    	if (! (bt instanceof StructType)) {
    		// quick check, if process expression can be used.
    		return new LeftHandSide[] { processLeftHandSide(lhs) };
    	}
    	StructType st = (StructType) bt;

        if (lhs instanceof VariableLHS) {
        	String id = ((VariableLHS) lhs).getIdentifier();
        	VariableLHS[] flattened = new VariableLHS[st.getFieldCount()];
        	for (int i = 0; i < flattened.length; i++) {
        		String ident = id + DOT + st.getFieldIds()[i];
        		IType type = st.getFieldType(i);
        		flattened[i] =
        			new VariableLHS(lhs.getLocation(), type, ident);
        	}
        	return flattened;
        } else if (lhs instanceof ArrayLHS) {
            ArrayLHS alhs = (ArrayLHS) lhs;
        	LeftHandSide[] arrays = expandLeftHandSide(alhs.getArray());
        	Expression[] indices = processExpressions(alhs.getIndices());
        	LeftHandSide[] result = new LeftHandSide[arrays.length];
        	for (int i = 0; i < result.length; i++) {
        		IType resultType = st.getFieldType(i);
        		result[i] = new ArrayLHS
        				(alhs.getLocation(), resultType, arrays[i], indices);
        	}
        	return result;
        } else if (lhs instanceof StructLHS) {
        	StructLHS slhs = (StructLHS) lhs;
        	LeftHandSide[] allFields = expandLeftHandSide(slhs.getStruct());
        	StructType subType = (StructType) flattenType(slhs.getStruct().getType());
        	assert (subType.getFieldCount() == allFields.length);
        	int start = -1, end = -1;
        	for (int i = 0; i < subType.getFieldCount(); i++) {
        		if (subType.getFieldIds()[i].startsWith(slhs.getField()+DOT)) {
        			if (start == -1)
        				start = i;
        			end = i;
        		}
        	}
        	if (start == -1)
        		throw new RuntimeException("Field name not found in "+lhs);
        	LeftHandSide[] result = new LeftHandSide[end-start+1];
        	System.arraycopy(allFields, start, result, 0, end - start + 1);
        	return result;
        } else {
        	throw new AssertionError("Strange LHS "+lhs);
        }
    }
    
    /**
     * Processes a list of left hand sides.  This will expand lhs that
     * have a struct type to multiple lhs, one for each field.  This
     * can thus be used to expand the lhs of an assignment of procedure
     * call or the havoc or modified list.
     * 
     * @param lhss  the list of left hand sides to process.
     * @return A list containing the processed lhs. 
     */
    @Override
    protected LeftHandSide[] processLeftHandSides(LeftHandSide[] lhss) {
    	ArrayList<LeftHandSide> flat = new ArrayList<LeftHandSide>();
    	for (LeftHandSide e : lhss) {
    		flat.addAll(Arrays.asList(expandLeftHandSide(e)));
    	}
    	return flat.toArray(new LeftHandSide[flat.size()]);
    }

    /**
     * Expand function declaration s.t.:
     * <ul>
     * <li>iff return value is of struct type: declare a function for each
     * struct field recursively. <br />
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
     * <li>for each param p : if p is of struct type: expand to multiple in
     * params</li>
     * <li>otherwise: return function declaration as is.</li>
     * <ul>
     * 
     * @param funDecl
     *            the function declaration to expand.
     * @return new function declarations.
     */
    private Declaration[] expandFunctionDeclaration(
            final FunctionDeclaration funDecl) {
    	IType retType = funDecl.getOutParam().getType().getBoogieType();
    	BoogieType bt = flattenType(retType);
    	if (!(bt instanceof StructType)) {
    		// quick check, if processDeclaration can be used.
    		return new Declaration[] { processDeclaration(funDecl) };
    	}
    	StructType st = (StructType) bt;
    	Declaration[] newDecls = new Declaration[st.getFieldCount()];
    	Expression[] bodies;
    	if (funDecl.getBody() == null)
    		bodies = new Expression[st.getFieldCount()];
    	else
    		bodies = expandExpression(funDecl.getBody());
    	VarList[] newInParams = processVarLists(funDecl.getInParams());
    	
    	for (int i = 0; i < newDecls.length; i++) {
    		ILocation loc = funDecl.getOutParam().getLocation(); 
        	VarList newOutParam = new VarList
        		(loc, funDecl.getOutParam().getIdentifiers(), 
        		 st.getFieldType(i).toASTType(loc));
    		newDecls[i] = new FunctionDeclaration
    			(funDecl.getLocation(), funDecl.getAttributes(),
    			funDecl.getIdentifier() + DOT + st.getFieldIds()[i],
    			funDecl.getTypeParams(),  newInParams, newOutParam, bodies[i]);
    	}
    	return newDecls;
    }
}
