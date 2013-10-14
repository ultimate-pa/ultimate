/**
 * Class that handles expanding of structs into normal variables.
 */
package de.uni_freiburg.informatik.ultimate.boogie.preprocessor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.ConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.StructType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieTransformer;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayStoreExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssignmentStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Body;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.CallStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.FunctionDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructConstructor;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.TypeDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
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
 * @author Markus Lindenmann
 * @date 26.08.2012
 */
public class StructExpander extends BoogieTransformer implements
        IUnmanagedObserver {
    /**
     * String holding ~.
     */
    private static final String TILDE = "~";
    /**
     * String holding a period / dot.
     */
    private static final String DOT = ".";
    /**
     * Empty String.
     */
    private static final String EMPTY_STRING = "";
    /**
     * Holds all identifiers, that are of type struct or struct[].
     */
    private HashMap<String, IType> globalStructTypes;
    /**
     * Holds all identifiers, that are of type struct or struct[].
     */
    private HashMap<String, IType> localStructTypes;

    /**
     * Converts an IType to a corresponding ASTType.
     * 
     * @param t
     *            the IType to convert.
     * @param loc
     *            the location for the new ASTTypes.
     * @return the generated ASTType.
     */
    private ASTType getASTType(IType t, ILocation loc) {
        IType type = t;
        if (type instanceof ConstructedType) {
            type = ((ConstructedType) type).getUnderlyingType();
        }
        if (type instanceof PrimitiveType) {
            PrimitiveType pt = (PrimitiveType) type;
            return new de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType(
                    loc, pt, pt.toString());
        } else if (type instanceof ArrayType) {
            ArrayType at = (ArrayType) type;
            ASTType vt = getASTType(at.getValueType(), loc);
            ASTType[] idc = new ASTType[at.getIndexCount()];
            for (int i = 0; i < at.getIndexCount(); i++) {
                idc[i] = getASTType(at.getIndexType(i), loc);
            }
            return new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType(
                    loc, type, new String[0], idc, vt);
        } else if (type instanceof StructType) {
            StructType st = (StructType) type;
            VarList[] fields = new VarList[st.getFieldCount()];
            for (int i = 0; i < st.getFieldCount(); i++) {
                fields[i] = new VarList(loc,
                        new String[] { st.getFieldIds()[i] }, getASTType(
                                st.getFieldTypes()[i], loc));
            }
            return new de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType(
                    loc, type, fields);
        } else {
            assert false;
            throw new UnsupportedOperationException("Not yet implemented!");
        }
    }

    /**
     * Checks all array indices, whether one is of struct type.
     * 
     * @param t
     *            the type to check.
     * @return true iff t is an ArrayType and at least one index is of struct
     *         type.
     */
    private static boolean isAnIndexAStruct(final IType t) {
        IType it = t;
        if (it instanceof ConstructedType)
            it = ((ConstructedType) it).getUnderlyingType();
        if (it instanceof ArrayType) {
            ArrayType at = (ArrayType) it;
            for (int i = 0; i < at.getIndexCount(); i++) {
                if (isNamedTypeStructOrStructArray(at.getIndexType(i))) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Checks all array indices, whether one is of struct type.
     * 
     * @param aae
     *            the array access expression to check.
     * @return true iff t is an ArrayType and at least one index is of struct
     *         type.
     */
    private static boolean isAnIndexAStruct(final ArrayAccessExpression aae) {
        for (Expression e : aae.getIndices()) {
            if (isNamedTypeStructOrStructArray(e.getType())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Checks whether the type is an ArrayType, and if the valueType is instance
     * of StructType.
     * 
     * @param t
     *            the type to check.
     * @return true iff (type is an ArrayType and valueType is StructType).
     */
    private static boolean isArrayOfStruct(final IType t) {
        if (t instanceof ArrayType) {
            IType vt = ((ArrayType) t).getValueType();
            if (vt instanceof ConstructedType) {
                vt = ((ConstructedType) vt).getUnderlyingType();
            }
            if (vt instanceof StructType) {
                return true;
            }
        }
        return false;
    }

    /**
     * Determines, whether the given type is a NamedType and referring to a type
     * using structs.
     * 
     * @param t
     *            the type to decide on.
     * @return true iff the underlying type is using structs.
     */
    private static boolean isNamedTypeStructOrStructArray(final IType t) {
        if (t instanceof StructType)
            return true;
        if (isArrayOfStruct(t))
            return true;
        if (t instanceof ConstructedType) {
            ConstructedType ct = (ConstructedType) t;
            if (ct.getUnderlyingType() instanceof StructType)
                return true;
            if (isArrayOfStruct(ct))
                return true;
        }
        return false;
    }

    @Override
    public void init() {
        this.globalStructTypes = new HashMap<String, IType>();
        this.localStructTypes = new HashMap<String, IType>();
    }

    @Override
    public void finish() {
        this.globalStructTypes = null;
        this.localStructTypes = null;
    }

    @Override
    public WalkerOptions getWalkerOptions() {
        return null;
    }

    @Override
    public boolean performedChanges() {
        return true;
    }

    @Override
    public boolean process(IElement root) {
        if (root instanceof WrapperNode) {
            Unit unit = (Unit) ((WrapperNode) root).getBacking();
            ArrayList<Declaration> newDecls = new ArrayList<Declaration>();
            for (Declaration d : unit.getDeclarations()) {
                if (d instanceof FunctionDeclaration) {
                    ArrayList<Declaration> funcs = expandFunctionDeclaration((FunctionDeclaration) d);
                    newDecls.addAll(funcs);
                } else {
                    Declaration decl = processDeclaration(d);
                    if (decl != null)
                        newDecls.add(decl);
                }
            }
            unit.setDeclarations(newDecls.toArray(new Declaration[0]));
            return false;
        }
        return true;
    }

    @Override
    protected Specification processSpecification(Specification spec) {
        if (spec instanceof ModifiesSpecification) {
            HashSet<String> newIdsList = new HashSet<String>();
            String[] ids = ((ModifiesSpecification) spec).getIdentifiers();
            for (String id : ids) {
                if (globalStructTypes.containsKey(id)) {
                    IType varType = globalStructTypes.get(id);
                    IdentifierExpression idEx = new IdentifierExpression(
                            spec.getLocation(), varType, id);
                    for (Expression ide : expandExpression(idEx))
                        newIdsList.add(((IdentifierExpression) ide)
                                .getIdentifier());
                } else
                    newIdsList.add(id);
            }
            String[] newIds = newIdsList.toArray(new String[0]);
            if (ids != newIds)
                return new ModifiesSpecification(spec.getLocation(),
                        spec.isFree(), newIds);
            return spec;
        }
        return super.processSpecification(spec);
    }

    @Override
    protected Expression[] processExpressions(Expression[] exprs) {
        ArrayList<Expression> newExprs = new ArrayList<Expression>(exprs.length);
        for (Expression e : exprs)
            newExprs.addAll(expandExpression(e));
        Expression[] nExprs = newExprs.toArray(new Expression[0]);
        if (Arrays.equals(nExprs, exprs))
            return exprs;
        return nExprs;
    }

    @Override
    protected Statement processStatement(final Statement statement) {
        if (statement instanceof AssignmentStatement) {
            AssignmentStatement assign = (AssignmentStatement) statement;
            assert assign.getLhs().length == assign.getRhs().length;
            ArrayList<LeftHandSide> newLhs = new ArrayList<LeftHandSide>();
            Expression[] newRhs = processExpressions(assign.getRhs());
            for (int i = 0; i < assign.getLhs().length; i++) {
                LeftHandSide lhs = processLeftHandSide(assign.getLhs()[i]);
                assert lhs instanceof VariableLHS || lhs instanceof ArrayLHS;
                IType it = lhs.getType();
                if (it instanceof ConstructedType
                        && isNamedTypeStructOrStructArray(it))
                    it = ((ConstructedType) it).getUnderlyingType();
                if (it instanceof StructType || isArrayOfStruct(it)) {
                    if (lhs instanceof VariableLHS) {
                        String id = ((VariableLHS) lhs).getIdentifier();
                        ILocation loc = lhs.getLocation();
                        ArrayList<IdentifierExpression> ies = expandIType(loc,
                                lhs.getType(), id);
                        for (IdentifierExpression ie : ies)
                            newLhs.add(new VariableLHS(loc, ie.getType(), ie
                                    .getIdentifier()));
                    } else if (lhs instanceof ArrayLHS) {
                        assert lhs instanceof ArrayLHS;
                        LeftHandSide array = ((ArrayLHS) lhs).getArray();
                        assert array instanceof VariableLHS;
                        String id = ((VariableLHS) array).getIdentifier();
                        Expression[] idc = processExpressions(((ArrayLHS) lhs)
                                .getIndices());
                        ILocation loc = lhs.getLocation();
                        ArrayList<IdentifierExpression> ies = expandIType(loc,
                                lhs.getType(), id);
                        for (IdentifierExpression ie : ies) {
                            VariableLHS nVLhs = new VariableLHS(loc,
                                    ie.getType(), ie.getIdentifier());
                            newLhs.add(new ArrayLHS(loc, nVLhs, idc));
                        }
                    } else {
                        throw new AssertionError(
                                "Something went wrong during struct expansion");
                    }
                } else {
                    newLhs.add(processLeftHandSide(lhs));
                }
            }
            return new AssignmentStatement(assign.getLocation(),
                    newLhs.toArray(new LeftHandSide[0]), newRhs);
        } else if (statement instanceof CallStatement) {
            CallStatement cStmt = (CallStatement) statement;
            ILocation loc = cStmt.getLocation();
            ArrayList<String> newLhsL = new ArrayList<String>();
            for (String id : cStmt.getLhs()) {
                IType varType = null;
                if (localStructTypes.containsKey(id)) {
                    varType = localStructTypes.get(id);
                } else if (globalStructTypes.containsKey(id)) {
                    varType = globalStructTypes.get(id);
                } else {
                    newLhsL.add(id);
                    continue;
                }
                IdentifierExpression idEx = new IdentifierExpression(loc,
                        varType, id);
                for (Expression ide : expandExpression(idEx))
                    newLhsL.add(((IdentifierExpression) ide).getIdentifier());
            }
            String[] newLhs = newLhsL.toArray(new String[0]);
            Expression[] newArgs = processExpressions(cStmt.getArguments());
            if (newLhs.equals(cStmt.getLhs())
                    && newArgs.equals(cStmt.getArguments())) {
                return cStmt;
            }
            return new CallStatement(cStmt.getLocation(), cStmt.isForall(),
                    newLhs, cStmt.getMethodName(), newArgs);
        } else if (statement instanceof HavocStatement) {
            HavocStatement hStmt = (HavocStatement) statement;
            ILocation loc = hStmt.getLocation();
            ArrayList<String> newIdsL = new ArrayList<String>();
            for (String id : hStmt.getIdentifiers()) {
                IType varType = null;
                if (localStructTypes.containsKey(id)) {
                    varType = localStructTypes.get(id);
                } else if (globalStructTypes.containsKey(id)) {
                    varType = globalStructTypes.get(id);
                } else {
                    newIdsL.add(id);
                    continue;
                }
                IdentifierExpression idEx = new IdentifierExpression(loc,
                        varType, id);
                for (Expression ide : expandExpression(idEx))
                    newIdsL.add(((IdentifierExpression) ide).getIdentifier());
            }
            String[] newIds = newIdsL.toArray(new String[0]);
            if (Arrays.equals(newIds, hStmt.getIdentifiers())) {
                return hStmt;
            }
            return new HavocStatement(loc, newIds);
        }
        return super.processStatement(statement);
    }

    @Override
    protected LeftHandSide processLeftHandSide(final LeftHandSide lhs) {
        if (lhs instanceof StructLHS
                || (lhs instanceof ArrayLHS && ((ArrayLHS) lhs).getArray() instanceof StructLHS)) {
            LeftHandSide l = lhs;
            ArrayList<String> lhsList = new ArrayList<String>();
            ArrayList<Expression> arrayIndices = new ArrayList<Expression>();
            while (l instanceof ArrayLHS || l instanceof StructLHS) {
                if (l instanceof ArrayLHS) {
                    ArrayLHS alhs = (ArrayLHS) l;
                    if (alhs.getIndices() != null)
                        arrayIndices.addAll(Arrays
                                .asList(processExpressions(alhs.getIndices())));
                    l = alhs.getArray();
                } else if (l instanceof StructLHS) {
                    StructLHS slhs = (StructLHS) l;
                    lhsList.add(slhs.getField());
                    l = slhs.getStruct();
                }
            }
            assert l instanceof VariableLHS;
            lhsList.add(((VariableLHS) l).getIdentifier());
            Collections.reverse(lhsList);

            StringBuilder sb = new StringBuilder();
            final String sep = DOT;
            for (String s : lhsList)
                sb.append(sep).append(s);
            sb.replace(0, 1, EMPTY_STRING);
            VariableLHS vlhs = new VariableLHS(lhs.getLocation(), sb.toString());
            if (!arrayIndices.isEmpty()) {
                return new ArrayLHS(lhs.getLocation(), vlhs,
                        arrayIndices.toArray(new Expression[0]));
            }
            return vlhs;
        }
        return super.processLeftHandSide(lhs);
    }

    @Override
    protected Declaration processDeclaration(final Declaration d) {
        if (d instanceof VariableDeclaration) {
            return expandVariableDeclaration((VariableDeclaration) d, true);
        } else if (d instanceof Procedure) {
            localStructTypes.clear();
            Procedure p = (Procedure) d;
            VarList[] in = processVarLists(p.getInParams());
            VarList[] out = processVarLists(p.getOutParams());
            Specification[] specs = p.getSpecification();
            Specification[] newSpecs = specs != null ? processSpecifications(specs)
                    : null;
            Body body = p.getBody();
            Body newBody = body != null ? processBody(body) : null;
            Attribute[] newAttrs = processAttributes(p.getAttributes());
            return new Procedure(p.getLocation(), newAttrs, p.getIdentifier(),
                    p.getTypeParams(), in, out, newSpecs, newBody);
        } else if (d instanceof TypeDeclaration
                && (((TypeDeclaration) d).getSynonym() != null && isNamedTypeStructOrStructArray(((TypeDeclaration) d)
                        .getSynonym().getBoogieType()))) {
            return null;
        }
        return super.processDeclaration(d);
    }

    @Override
    protected VariableDeclaration processLocalVariableDeclaration(
            final VariableDeclaration local) {
        return (VariableDeclaration) expandVariableDeclaration(local, false);
    }

    @Override
    protected Expression processExpression(final Expression expr) {
        if (expr instanceof StructAccessExpression
                || (expr instanceof ArrayAccessExpression && ((ArrayAccessExpression) expr)
                        .getArray() instanceof StructAccessExpression)) {
            Expression e = expr;
            ArrayList<String> lhsList = new ArrayList<String>();
            ArrayList<Expression> arrayIndices = new ArrayList<Expression>();
            while (e instanceof ArrayAccessExpression
                    || e instanceof StructAccessExpression) {
                if (e instanceof ArrayAccessExpression) {
                    ArrayAccessExpression aae = (ArrayAccessExpression) e;
                    if (aae.getIndices() != null)
                        arrayIndices.addAll(Arrays
                                .asList(processExpressions(aae.getIndices())));
                    e = aae.getArray();
                } else if (e instanceof StructAccessExpression) {
                    StructAccessExpression sae = (StructAccessExpression) e;
                    lhsList.add(sae.getField());
                    e = sae.getStruct();
                }
            }
            assert e instanceof IdentifierExpression;
            lhsList.add(((IdentifierExpression) e).getIdentifier());
            Collections.reverse(lhsList);

            StringBuilder sb = new StringBuilder();
            for (String s : lhsList)
                sb.append(DOT).append(s);
            sb.replace(0, 1, EMPTY_STRING);
            Expression ide = new IdentifierExpression(expr.getLocation(),
                    expr.getType(), sb.toString());
            if (!arrayIndices.isEmpty())
                return new ArrayAccessExpression(e.getLocation(),
                        expr.getType(), ide,
                        arrayIndices.toArray(new Expression[0]));
            return ide;
        } else if (expr instanceof BinaryExpression) {
            BinaryExpression binexp = (BinaryExpression) expr;
            Operator op = binexp.getOperator();
            if (op == Operator.COMPEQ || op == Operator.COMPNEQ) {
                ILocation loc = expr.getLocation();
                Expression left = processExpression(binexp.getLeft());
                Expression right = processExpression(binexp.getRight());
                assert left.getType() == right.getType();
                Expression[] r, l;
                r = processExpressions(new Expression[] { left });
                l = processExpressions(new Expression[] { right });
                assert r.length == l.length;
                Operator concat;
                if (binexp.getOperator() == Operator.COMPEQ) {
                    concat = Operator.LOGICAND;
                } else {
                    concat = Operator.LOGICOR;
                }
                BinaryExpression bex = null;
                IType b = binexp.getType();
                for (int i = 0; i < r.length; i++) {
                    BinaryExpression inner = new BinaryExpression(loc, b, op,
                            l[i], r[i]);
                    if (i != 0) {
                        bex = new BinaryExpression(loc, b, concat, bex, inner);
                    } else {
                        bex = inner;
                    }
                }
                assert bex != null;
                return bex;
            }
        }
        return super.processExpression(expr);
    }

    @Override
    protected VarList[] processVarLists(VarList[] vls) {
        boolean changed = false;
        ArrayList<VarList> newVls = new ArrayList<VarList>();
        for (int i = 0; i < vls.length; i++) {
            IType it = vls[i].getType().getBoogieType();
            if (it instanceof ConstructedType
                    && isNamedTypeStructOrStructArray(it))
                it = ((ConstructedType) it).getUnderlyingType();
            if (it instanceof StructType) {
                newVls.addAll(expandStructTypeVarList(vls[i], EMPTY_STRING));
                changed = true;
            } else if (isArrayOfStruct(it)) {
                newVls.addAll(expandStructArrayTypeVarList(vls[i], EMPTY_STRING));
                changed = true;
            } else {
                VarList newVL = processVarList(vls[i]);
                newVls.add(newVL);
                if (newVL != vls[i])
                    changed = true;
            }
        }
        return changed ? newVls.toArray(new VarList[0]) : vls;
    }

    /**
     * Handles a variable declaration.
     * 
     * @param d
     *            the VariableDeclaration to process.
     * @param isGlobal
     *            whether the declaration is global or local.
     * @return the processed variable declaration.
     */
    private Declaration expandVariableDeclaration(final VariableDeclaration d,
            boolean isGlobal) {
        ArrayList<VarList> vars = new ArrayList<VarList>();
        boolean changed = false;
        for (VarList vl : ((VariableDeclaration) d).getVariables()) {
            IType it = vl.getType().getBoogieType();
            if (isNamedTypeStructOrStructArray(it) || isAnIndexAStruct(it)) {
                changed = true;
                if (it instanceof ConstructedType
                        && isNamedTypeStructOrStructArray(it))
                    it = ((ConstructedType) it).getUnderlyingType();
                if (isGlobal)
                    for (String id : vl.getIdentifiers())
                        globalStructTypes.put(id, it);
                else
                    for (String id : vl.getIdentifiers())
                        localStructTypes.put(id, it);
                if (it instanceof StructType)
                    vars.addAll(expandStructTypeVarList(vl, EMPTY_STRING));
                else
                    vars.addAll(expandStructArrayTypeVarList(vl, EMPTY_STRING));
            } else {
                vars.add(processVarList(vl));
            }
        }
        if (changed) {
            return new VariableDeclaration(d.getLocation(), d.getAttributes(),
                    vars.toArray(new VarList[0]));
        }
        return super.processDeclaration(d);
    }

    /**
     * Handles a array with value or index type struct.
     * 
     * @param vl
     *            the variable list.
     * @param pre
     *            the String prefix previously calculated.
     * @return expanded variable lists.
     */
    private ArrayList<VarList> expandStructArrayTypeVarList(final VarList vl,
            final String pre) {
        IType it = vl.getType().getBoogieType();
        assert isArrayOfStruct(it) || isAnIndexAStruct(it);
        ILocation loc = vl.getLocation();
        de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType at = (de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType) getASTType(
                it, loc);
        ArrayList<VarList> flatFields;
        if (it instanceof StructType || isArrayOfStruct(it)) {
            flatFields = expandStructTypeVarList(vl, pre);
        } else {
            flatFields = new ArrayList<VarList>();
            assert it instanceof ArrayType;
            ASTType valueType = ((de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType) vl
                    .getType()).getValueType();
            VarList value = new VarList(loc, vl.getIdentifiers(), valueType);
            flatFields.add(value);
        }
        ArrayList<ASTType> idcL = new ArrayList<ASTType>();
        for (ASTType ti : at.getIndexTypes()) {
            if (isNamedTypeStructOrStructArray(ti.getBoogieType())) {
                ArrayList<IdentifierExpression> ies = expandIType(loc,
                        ti.getBoogieType(), EMPTY_STRING);
                for (IdentifierExpression ie : ies) {
                    idcL.add(getASTType(ie.getType(), loc));
                }
            } else {
                idcL.add(ti);
            }
        }
        ASTType[] idc = idcL.toArray(new ASTType[0]);
        ArrayList<VarList> vars = new ArrayList<VarList>();
        for (VarList vlf : flatFields) {
            if (vlf.getType() instanceof de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType) {
                de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType fieldArray = (de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType) vlf
                        .getType();
                ArrayList<ASTType> eIdcL = new ArrayList<ASTType>();
                eIdcL.addAll(idcL);
                eIdcL.addAll(Arrays.asList(fieldArray.getIndexTypes()));
                ASTType[] eIdc = eIdcL.toArray(new ASTType[0]);
                vars.add(new VarList(
                        loc,
                        vlf.getIdentifiers(),
                        new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType(
                                loc, at.getTypeParams(), eIdc, fieldArray
                                        .getValueType())));
            } else {
                vars.add(new VarList(
                        loc,
                        vlf.getIdentifiers(),
                        new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType(
                                loc, at.getTypeParams(), idc, vlf.getType())));
            }
        }
        return vars;
    }

    /**
     * Handles a struct typed variable list.
     * 
     * @param vl
     *            the variable list.
     * @param pre
     *            the String prefix previously calculated.
     * @return expanded variable lists.
     */
    private ArrayList<VarList> expandStructTypeVarList(final VarList vl,
            final String pre) {
        IType it = vl.getType().getBoogieType();
        ILocation loc = vl.getLocation();
        if (it instanceof ConstructedType) {
            it = ((ConstructedType) it).getUnderlyingType();
        }
        assert it instanceof StructType || isArrayOfStruct(it);
        StructType st = null;
        if (it instanceof StructType) {
            st = (StructType) it;
        } else if (isArrayOfStruct(it)) {
            IType t = ((ArrayType) it).getValueType();
            if (t instanceof ConstructedType) {
                t = ((ConstructedType) t).getUnderlyingType();
            }
            st = (StructType) t;
        }
        assert st != null;
        de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType struct = (de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType) getASTType(
                st, loc);
        ArrayList<VarList> vars = new ArrayList<VarList>();
        for (String s : vl.getIdentifiers()) {
            for (VarList f : struct.getFields()) {
                for (String vlfid : f.getIdentifiers()) {
                    StringBuilder sb = new StringBuilder(pre).append(s).append(
                            DOT);
                    if (f.getType() instanceof de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructType) {
                        vars.addAll(expandStructTypeVarList(f, sb.toString()));
                    } else if (isArrayOfStruct(f.getType().getBoogieType())) {
                        vars.addAll(expandStructArrayTypeVarList(f,
                                sb.toString()));
                    } else {
                        VarList vlf = processVarList(f);
                        sb.append(vlfid);
                        vars.add(new VarList(vlf.getLocation(),
                                new String[] { sb.toString() }, vlf.getType()));
                    }
                }
            }
        }
        return vars;
    }

    /**
     * Expands a boogie type. E.g. struct -> all fields OR Struct[] -> arrays of
     * struct fields.
     * 
     * @param loc
     *            location for new identifier expressions.
     * @param bt
     *            the type.
     * @param pre
     *            previously calculated, left side id.
     * @return a list of id expressions.
     */
    private ArrayList<IdentifierExpression> expandIType(ILocation loc,
            final IType bt, String pre) {
        ArrayList<IdentifierExpression> ies = new ArrayList<IdentifierExpression>();
        IType ibt = bt;
        if (ibt instanceof ConstructedType)
            ibt = ((ConstructedType) ibt).getUnderlyingType();
        if (ibt instanceof StructType || isArrayOfStruct(ibt)) {
            StructType st = null;
            if (ibt instanceof StructType) {
                st = (StructType) ibt;
            } else if (isArrayOfStruct(ibt)) {
                IType t = ((ArrayType) ibt).getValueType();
                if (t instanceof ConstructedType) {
                    t = ((ConstructedType) t).getUnderlyingType();
                }
                st = (StructType) t;
            }
            assert st != null;
            String acc = new StringBuilder(pre).append(DOT).toString();
            for (String f : st.getFieldIds()) {
                String fieldAcc = new StringBuilder(acc).append(f).toString();
                ies.addAll(expandIType(loc, st.getFieldType(f), fieldAcc));
            }
        } else {
            ies.add(new IdentifierExpression(loc, ibt, pre));
        }
        return ies;
    }

    /**
     * Expands the given expression in case the underlying type is a struct.
     * Otherwise this returns a singleton list with the processsed expression.
     * 
     * @param e  the expression to expand.
     * @return A list containing an expanded expression for every field
     *   in the type of the original expression.
     */
    private ArrayList<Expression> expandExpression(Expression e) {
        ArrayList<Expression> newExprs = new ArrayList<Expression>();
        if (e instanceof IdentifierExpression) {
            if (!isNamedTypeStructOrStructArray(e.getType())) {
                newExprs.add((IdentifierExpression) processExpression(e));
            } else {
                String id = ((IdentifierExpression) e).getIdentifier();
                newExprs.addAll(expandIType(e.getLocation(), e.getType(), id));
            }
            return newExprs;
        } else if (e instanceof ArrayAccessExpression
                && (e.getType() instanceof StructType || isAnIndexAStruct((ArrayAccessExpression) e))) {
            // e.g. d[0] = e[1], where both are structs!
            ArrayAccessExpression aae = (ArrayAccessExpression) e;
            Expression left = processExpression(aae.getArray());
            assert left instanceof IdentifierExpression;
            IdentifierExpression leftIe = (IdentifierExpression) left;
            Expression[] newIdc = processExpressions(aae.getIndices());
            ArrayList<IdentifierExpression> ies = expandIType(
                    aae.getLocation(), aae.getType(), leftIe.getIdentifier());
            for (IdentifierExpression ie : ies)
                newExprs.add(new ArrayAccessExpression(aae.getLocation(), ie
                        .getType(), ie, newIdc));
            return newExprs;
        } else if (e instanceof FunctionApplication
                && isNamedTypeStructOrStructArray(((FunctionApplication) e)
                        .getType())) {
            // we found a function call returning struct
            // struct s := func(); => s!f1, s!f2 := funcf1(), funcf2();
            FunctionApplication oldFA = (FunctionApplication) e;
            ILocation loc = e.getLocation();
            ArrayList<IdentifierExpression> ies = expandIType(loc, e.getType(),
                    EMPTY_STRING);
            for (IdentifierExpression ie : ies) {
                assert ie.getIdentifier().startsWith(DOT);
                String id = ie.getIdentifier().substring(1);
                Expression[] args = processExpressions(oldFA.getArguments());
                Expression fa = new FunctionApplication(loc, ie.getType(),
                        oldFA.getIdentifier() + TILDE + id, args);
                newExprs.add(fa);
            }
            return newExprs;
        } else if (e instanceof ArrayStoreExpression
                && (e.getType() instanceof StructType || isAnIndexAStruct(e
                        .getType()))) {
            ArrayStoreExpression ase = (ArrayStoreExpression) e;
            Expression left = processExpression(ase.getArray());
            Expression i = left;
            if (i instanceof UnaryExpression) {
                i = ((UnaryExpression) i).getExpr();
            }
            assert i instanceof IdentifierExpression;
            IdentifierExpression leftIe = (IdentifierExpression) i;
            Expression[] newIdc = processExpressions(ase.getIndices());
            Expression[] newVal = processExpressions(new Expression[] { ase
                    .getValue() });
            ILocation l = ase.getLocation();
            ArrayList<IdentifierExpression> ies = expandIType(l, ase.getType(),
                    leftIe.getIdentifier());
            assert ies.size() == newVal.length;
            for (int k = 0; k < ies.size(); k++) {
                Expression ie = ies.get(k);
                Expression val = newVal[k];
                Expression newArray; 
                if (left instanceof UnaryExpression) {
                	newArray = new UnaryExpression(l, left.getType(),
                            ((UnaryExpression) left).getOperator(), ie);
                } else {
                	newArray = ie;
                }
            	Expression j = new ArrayStoreExpression(l, newArray.getType(), 
            			newArray, newIdc, val);
                newExprs.add(j);
            }
            return newExprs;
        } else if (e instanceof StructConstructor) {
        	Expression[] values = ((StructConstructor) e).getFieldValues();
        	ArrayList<Expression> result = new ArrayList<Expression>();
        	for (Expression val : values) {
        		result.addAll(expandExpression(val));
        	}
        	return result;
        }
        newExprs.add(processExpression(e));
        return newExprs;
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
    private ArrayList<Declaration> expandFunctionDeclaration(
            final FunctionDeclaration funDecl) {
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
        VarList[] in = processVarLists(funDecl.getInParams());
        VarList out = funDecl.getOutParam();
        if (isNamedTypeStructOrStructArray(out.getType().getBoogieType())) {
            // declare function for each return value!
            ILocation loc = out.getLocation();
            ArrayList<IdentifierExpression> ies = expandIType(loc, out
                    .getType().getBoogieType(), EMPTY_STRING);
            for (IdentifierExpression ie : ies) {
                assert ie.getIdentifier().startsWith(DOT);
                assert funDecl.getBody() == null;
                String id = ie.getIdentifier().substring(1);
                ASTType t = getASTType(ie.getType(), loc);
                out = new VarList(loc, new String[] { id }, t);
                decl.add(new FunctionDeclaration(funDecl.getLocation(), funDecl
                        .getAttributes(), funDecl.getIdentifier() + TILDE + id,
                        funDecl.getTypeParams(), in, out));
            }
        } else {
            decl.add(new FunctionDeclaration(funDecl.getLocation(), funDecl
                    .getAttributes(), funDecl.getIdentifier(), funDecl
                    .getTypeParams(), in, out, funDecl.getBody()));
        }
        return decl;
    }
}
