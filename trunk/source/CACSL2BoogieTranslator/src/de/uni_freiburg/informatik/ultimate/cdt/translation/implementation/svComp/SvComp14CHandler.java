/**
 * CHandler variation for the SV-COMP 2014.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.cdt.core.dom.ast.IASTBinaryExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTInitializerClause;
import org.eclipse.cdt.core.dom.ast.IASTLabelStatement;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.CHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType.Type;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPointer;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultSkip;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler.SVCompArrayHandler;
//import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler.SVCompFunctionHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ConvExpr;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.annotation.Overapprox;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssumeStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Attribute;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.HavocStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IfStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.NamedType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.WildcardExpression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.Backtranslator;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.Check.Spec;

/**
 * @author Markus Lindenmann
 * @date 12.6.2012
 */
public class SvComp14CHandler extends CHandler {
    /**
     * The string representing SV-Comp's error method.
     */
    private static final String ERROR_STRING = "__VERIFIER_error";
    /**
     * The string representing SV-Comp's havoc method.
     */
    private static final String NONDET_STRING = "__VERIFIER_nondet_";
    /**
     * Nondet_X | X in {int, float, char, short, long, pointer}
     */
    private static final String[] NONDET_TYPE_STRINGS = { "int", "long",
            "float", "char", "short", "pointer" };
    /**
     * The string representing SV-Comp's assert method.
     */
    private static final String ASSUME_STRING = "__VERIFIER_assume";

    

    /**
     * Constructor.
     * 
     * @param main
     *            a reference to the main dispatcher.
     */
    public SvComp14CHandler(Dispatcher main, Backtranslator backtranslator) {
        super(main, backtranslator, false);
        super.arrayHandler = new SVCompArrayHandler();
//        super.functionHandler = new SVCompFunctionHandler();
    }

//    @Override
//    public Result visit(Dispatcher main, IASTLabelStatement node) {
//        ResultExpression r = (ResultExpression) super.visit(main, node);
//        String label = node.getName().toString();
//        if (label.equals(ERROR_STRING)) {
//            Check check = new Check(Spec.ERROR_Function);
//            CACSLLocation loc = new CACSLLocation(node, check);
//            AssertStatement assertStmt = new AssertStatement(loc,
//                    new BooleanLiteral(loc, new InferredType(Type.Boolean),
//                            false));
//            check.addToNodeAnnot(assertStmt);
//            // We do not add the assert(false) directly, but add an 
//            // nondeterministic if that contains this assert.
//            // Adding the assert(false) directly would leads to an unsound
//            // nontermination analysis.
//            IfStatement ifStatement = new IfStatement(loc, 
//            		new WildcardExpression(loc), 
//            		new Statement[] { assertStmt }, new Statement[0]);
//            r.stmt.add(1, ifStatement);
//        }
//        return r;
//    }

    //
    // __VERIFIER_assume(EXPR) && skip VERIFIER_nondet_X()
    //

    @Override
    public Result visit(Dispatcher main, IASTFunctionCallExpression node) {
        ILocation loc = new CACSLLocation(node);
        String methodName = node.getFunctionNameExpression().getRawSignature();

        ArrayList<Statement> stmt = new ArrayList<Statement>();
        ArrayList<Declaration> decl = new ArrayList<Declaration>();
		Map<VariableDeclaration, ILocation> auxVars = 
				new HashMap<VariableDeclaration, ILocation>();
		ArrayList<Overapprox> overappr = new ArrayList<Overapprox>();
        LRValue returnValue = null;
        
        if (methodName.equals(ERROR_STRING)) {
            Check check = new Check(Spec.ERROR_Function);
            AssertStatement assertStmt = new AssertStatement(loc,
                    new BooleanLiteral(loc, new InferredType(Type.Boolean),
                            false));
            check.addToNodeAnnot(assertStmt);
            // We do not add the assert(false) directly, but add an 
            // nondeterministic if that contains this assert.
            // Adding the assert(false) directly would leads to an unsound
            // nontermination analysis.
            IfStatement ifStatement = new IfStatement(loc, 
            		new WildcardExpression(loc), 
            		new Statement[] { assertStmt }, new Statement[0]);
            stmt.add(ifStatement);
            return new ResultExpression(stmt, returnValue, decl, auxVars,
                    overappr);
        }
        if (methodName.equals(ASSUME_STRING)) {
            ArrayList<Expression> args = new ArrayList<Expression>();
            for (IASTInitializerClause inParam : node.getArguments()) {
                ResultExpression in = ((ResultExpression) main
                        .dispatch(inParam)).switchToRValueIfNecessary(main, memoryHandler, structHandler, loc);
                if (in.lrVal.getValue() == null) {
                    String msg = "Incorrect or invalid in-parameter! "
                            + loc.toString();
                    throw new IncorrectSyntaxException(loc, msg);
                }
                args.add(in.lrVal.getValue());
                stmt.addAll(in.stmt);
                decl.addAll(in.decl);
                auxVars.putAll(in.auxVars);
                overappr.addAll(in.overappr);
            }
            assert args.size() == 1; // according to SV-Comp specification!
            stmt.add(new AssumeStatement(loc,
            		ConvExpr.toBoolean(loc, new RValue(args.get(0), 
            				new CPrimitive(PRIMITIVE.INT))).getValue()));
            assert (main.isAuxVarMapcomplete(decl, auxVars));
            return new ResultExpression(stmt, returnValue, decl, auxVars,
                    overappr);
        }
        for (String t : NONDET_TYPE_STRINGS)
            if (methodName.equals(NONDET_STRING + t)) {
//                final InferredType type; 
                final ASTType type; 
                CType cType;
                if (t.equals("float")) {
//                	type = new InferredType(Type.Real);
                	type = new PrimitiveType(loc, SFO.REAL);
                	cType = new CPrimitive(PRIMITIVE.FLOAT);
                } else if (t.equals("pointer")) {
//                    type = new InferredType(Type.Pointer);
        			NamedType boogiePointerType = 
        					new NamedType(null, new InferredType(Type.Struct), SFO.POINTER, new ASTType[0]);
                	type = boogiePointerType;
                    cType = new CPointer(new CPrimitive(PRIMITIVE.VOID));
                } else {
//                	type = new InferredType(Type.Integer);
                	type = new PrimitiveType(loc, SFO.INT);
                	cType = new CPrimitive(PRIMITIVE.INT);
                }
                String tmpName = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
                VariableDeclaration tVarDecl = SFO.getTempVarVariableDeclaration(tmpName, type, loc);
                decl.add(tVarDecl);
                auxVars.put(tVarDecl, loc);
//                returnValue = new RValue(new IdentifierExpression(loc, type, tmpName), cType);
                returnValue = new RValue(new IdentifierExpression(loc, tmpName), cType);
                assert (main.isAuxVarMapcomplete(decl, auxVars));
                return new ResultExpression(stmt, returnValue, decl, auxVars,
                        overappr);
            }
        if (methodName.equals("printf")) {
            // skip if parent of parent is CompoundStatement
            // otherwise, replace by havoced variable
            if (node.getParent().getParent() instanceof IASTCompoundStatement) {
                return new ResultSkip();
            }
            InferredType type = new InferredType(Type.Integer);
            ASTType tempType = new PrimitiveType(loc, type, type.toString());
            String tId = main.nameHandler.getTempVarUID(SFO.AUXVAR.NONDET);
            VariableDeclaration tVarDecl = new VariableDeclaration(
            		loc, new Attribute[0],
                    new VarList[] { new VarList(loc, new String[] {tId}, tempType) });
            auxVars.put(tVarDecl, loc);
            decl.add(tVarDecl);
            stmt.add(new HavocStatement(loc, new VariableLHS[] { new VariableLHS(loc, tId)}));
            returnValue = new RValue(new IdentifierExpression(loc, type, tId, null), null);
            assert (main.isAuxVarMapcomplete(decl, auxVars));
            return new ResultExpression(stmt, returnValue, decl, auxVars,
                    overappr);
        }
        return super.visit(main, node);
    }

    //
    // VERIFIER_nondet_X()
    //

    @Override
    public Result visit(Dispatcher main, IASTBinaryExpression node) {
//        if (node.getOperator() == IASTBinaryExpression.op_assign
//                && node.getOperand2() instanceof IASTFunctionCallExpression
//                && ((IASTFunctionCallExpression) node.getOperand2())
//                        .getFunctionNameExpression().getRawSignature()
//                        .equalsIgnoreCase("malloc")) {
//            return new ResultSkip();
//        } // else
        Result r = super.visit(main, node);
        if (node.getOperator() == IASTBinaryExpression.op_divide
                || node.getOperator() == IASTBinaryExpression.op_divideAssign) {
            // remove division by zero asserts
            assert r instanceof ResultExpression;
            ResultExpression rex = (ResultExpression) r;
            Iterator<Statement> it = rex.stmt.iterator();
            while (it.hasNext())
                if (it.next() instanceof AssertStatement)
                    it.remove();
        }
        return r;
    }

//    @Override
//    public Result visit(Dispatcher main, IASTSimpleDeclaration node) {
//        CACSLLocation loc = new CACSLLocation(node);
//        Map<VariableDeclaration, CACSLLocation> auxVars = new HashMap<VariableDeclaration, CACSLLocation>();
//        if (node.getDeclarators() != null && node.getDeclarators().length > 0) {
//            // we decide on the first declarator ... [0] does NOT mean, that
//            // only the first declarator is handled!
//            IASTDeclarator cDecl = node.getDeclarators()[0];
//            if (cDecl instanceof IASTFunctionDeclarator) {
//                if (node.getParent() instanceof IASTCompositeTypeSpecifier) {
//                    ArrayList<Declaration> decl = new ArrayList<Declaration>();
//                    String methodName = ((IASTFunctionDeclarator) node
//                            .getDeclarators()[0]).getNestedDeclarator()
//                            .getName().toString();
//                    VarList v = new VarList(loc, new String[] { methodName },
//                            new PrimitiveType(loc, new InferredType(
//                                    Type.Integer), SFO.INT));
//                    decl.add(new VariableDeclaration(loc, new Attribute[0],
//                            new VarList[] { v }));
//                    return new ResultExpression(new ArrayList<Statement>(),
//                            null, decl, new HashMap<VariableDeclaration, CACSLLocation>(0));
//                }
//                // extracted for readability only ... could be in lined again
//                String methodName = ((IASTFunctionDeclarator) node
//                        .getDeclarators()[0]).getName().toString();
//                if (methodName.equals(ASSUME_STRING))
//                    return new ResultSkip();
//                for (String t : NONDET_TYPE_STRINGS)
//                    if (methodName.equals(NONDET_STRING + t))
//                        return new ResultSkip(); // handled in assignment stmt!
//                return functionHandler.handleFunctionDeclaration(main,
//                        super.contract, node);
//            } else if (cDecl instanceof IASTArrayDeclarator) {
//                // extracted for readability only ... could be in lined again
//                return arrayHandler
//                        .handleArrayDeclaration(main, structHandler, node,
//                                super.globalVariables,
//                                super.globalVariablesInits);
//            }
//            if (node.getDeclSpecifier() == null) {
//                String msg = "This statement can be removed!";
//                Dispatcher.unsoundnessWarning(loc, msg, "empty!");
//                return new ResultSkip();
//            }
//        }
//
//        // Here we handle "normal variable" declaration, all other cases
//        // should be caught before
//        Result r = main.dispatch(node.getDeclSpecifier());
//        assert r instanceof ResultSkip || r instanceof ResultTypes;
//        if (r instanceof ResultTypes) {
//            if (((ResultTypes) r).isVoid) {
//                for (IASTDeclarator d : node.getDeclarators()) {
//                    if (d.getPointerOperators().length > 0) {
//                        // this looks like a void pointer - translate the type
//                        // to int.
//                        r = new ResultTypes(new PrimitiveType(loc,
//                                new InferredType(Type.Integer), SFO.INT),
//                                false, false, null);
//                        break;
//                    }
//                }
//            } else {
//                for (IASTDeclarator d : node.getDeclarators()) {
//                    if (d.getPointerOperators().length > 0) {
//                        r = new ResultTypes(((ResultTypes) r).getType(), false,
//                                false, null);
//                        break;
//                    }
//                }
//            }
//        }
//        if (r instanceof ResultSkip) {
//            return r;
//        } else if (r instanceof ResultTypes) {
//    		Map<VariableDeclaration, CACSLLocation> emptyAuxVars = 
//    				new HashMap<VariableDeclaration, CACSLLocation>();
//            ResultExpression result = new ResultExpression(null, emptyAuxVars);
//            ResultTypes resType = (ResultTypes) r;
//            ResultExpression staticVarStorage = new ResultExpression(null, emptyAuxVars);
//            boolean isGlobal = node.getParent() == node.getTranslationUnit();
//            if (node.getParent() == node.getTranslationUnit()) {
//                result.decl.addAll(((ResultTypes) r).typeDeclarations);
//            } else if (!((ResultTypes) r).typeDeclarations.isEmpty()) {
//                String msg = "Unexpected location for a typedef!";
//                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
//                throw new UnsupportedSyntaxException(msg);
//            }
//            SKIP_INIT: for (IASTDeclarator d : node.getDeclarators()) {
//                String cId = d.getName().getRawSignature();
//                // Get the type of this variable
//                assert resType.getType() != null;
//                String bId = main.nameHandler.getUniqueIdentifier(node, cId,
//                        symbolTable.getCompoundCounter());
//                ASTType type = resType.getType();
//                if (main.typeHandler.isStructDeclaration()) {
//                    // store C variable information into this result, as this is
//                    // a struct field! We need this information to build the
//                    // structs C variable information recursively.
//                    assert resType.cvar != null;
//                    result.declCTypes.add(resType.cvar);
//                }
//                VarList var = new VarList(loc, new String[] { bId }, type);
//                Attribute[] attr = new Attribute[0];
//                if (resType.isConst) {
//                    String msg = "Const declaration dropped!";
//                    Dispatcher
//                            .error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
//                }
//                VariableDeclaration decl = new VariableDeclaration(loc, attr,
//                        new VarList[] { var });
//                symbolTable.put(cId, new SymbolTableValue(bId, decl, isGlobal,
//                        resType.cvar));
//                if (resType.cvar.isStatic() && !isGlobal) {
//                    staticVarStorage.decl.add(decl);
//                } else {
//                    result.decl.add(decl);
//                }
//                // Handle initializer clause
//                if (d.getInitializer() != null) {
//                    if (d.getInitializer().getChildren().length > 0) {
//                        for (IASTNode n : d.getInitializer().getChildren()) {
//                            if (n instanceof IASTFunctionCallExpression
//                                    && ((IASTFunctionCallExpression) n)
//                                            .getFunctionNameExpression()
//                                            .getRawSignature()
//                                            .equalsIgnoreCase("malloc")) {
//                                continue SKIP_INIT;
//                            } else if (n instanceof IASTCastExpression) {
//                                IASTCastExpression ce = (IASTCastExpression) n;
//                                for (IASTNode ne : ce.getChildren()) {
//                                    if (ne instanceof IASTFunctionCallExpression
//                                            && ((IASTFunctionCallExpression) ne)
//                                                    .getFunctionNameExpression()
//                                                    .getRawSignature()
//                                                    .equalsIgnoreCase("malloc")) {
//                                        continue SKIP_INIT;
//                                    }
//                                }
//                            }
//                        }
//                    }
//                    if (type instanceof StructType) {
//                        Result initializer = main.dispatch(d.getInitializer());
//                        if (initializer instanceof ResultExpressionListRec) {
//                            ResultExpressionListRec relr = ((ResultExpressionListRec) initializer);
//                            VariableLHS lhs = new VariableLHS(loc,
//                                    new InferredType(type), bId);
//                            CType cvar = resType.cvar;
//                            if (cvar instanceof CNamed) {
//                                cvar = ((CNamed) cvar).getUnderlyingType();
//                            }
//                            assert cvar instanceof CStruct;
//                            ResultExpression init = structHandler
//                                    .handleStructInit(main, arrayHandler, loc,
//                                            (StructType) type, (CStruct) cvar,
//                                            lhs, relr,
//                                            new ArrayList<Integer>(), -1);
//                            assert init.expr == null && init.decl.isEmpty();
//                            if (resType.cvar.isStatic() && !isGlobal) {
//                                staticVarStorage.stmt.addAll(init.stmt);
//                            } else {
//                                result.stmt.addAll(init.stmt);
//                            }
//                        }
//                    } else { // it should be a "normal variable"
//                        ResultExpression rExpr = ((ResultExpression) (main
//                                .dispatch(d.getInitializer())));
//                        rExpr.expr = main.typeHandler.checkBooleanAssignment(
//                                loc, type, rExpr.expr);
//                        Expression[] rhs = new Expression[] { rExpr.expr };
//                        VariableLHS[] lhs = new VariableLHS[] { new VariableLHS(
//                                loc, bId) };
//                        AssignmentStatement as = new AssignmentStatement(loc,
//                                lhs, rhs);
//                        if (resType.cvar.isStatic() && !isGlobal) {
//                            staticVarStorage.decl.addAll(rExpr.decl);
//                            staticVarStorage.stmt.addAll(rExpr.stmt);
//                            staticVarStorage.stmt.add(as);
//                        } else {
//                            result.decl.addAll(rExpr.decl);
//                            result.stmt.addAll(rExpr.stmt);
//                            result.stmt.add(as);
//                            auxVars.putAll(rExpr.auxVars);
//                        }
//                    }
//                }
//            }
//            if (resType.cvar.isStatic() && !isGlobal) {
//                assert staticVarStorage.decl.size() > 0;
//                for (Declaration d : staticVarStorage.decl) {
//                    globalVariables.put(d, resType.cvar);
//                    assert d instanceof VariableDeclaration;
//                    VariableDeclaration vd = (VariableDeclaration) d;
//                    assert vd.getVariables().length == 1;
//                    assert vd.getVariables()[0].getIdentifiers().length == 1;
//                    String lhsId = vd.getVariables()[0].getIdentifiers()[0];
//                    ArrayList<Statement> init = new ArrayList<Statement>();
//                    for (ListIterator<Statement> iter = staticVarStorage.stmt
//                            .listIterator(staticVarStorage.stmt.size()); iter
//                            .hasPrevious();) {
//                        Statement s = iter.previous();
//                        assert s instanceof AssignmentStatement;
//                        AssignmentStatement as = (AssignmentStatement) s;
//                        assert as.getLhs().length == 1;
//                        if (BoogieASTUtil.getLHSId(as.getLhs()[0])
//                                .equals(lhsId)) {
//                            init.add(as);
//                            iter.remove();
//                        }
//                    }
//                    globalVariablesInits.put(d, init);
//                }
//                assert staticVarStorage.stmt.isEmpty();
//            }
//            result.stmt.addAll(Dispatcher.createHavocsForAuxVars(auxVars));
//            return result;
//        }
//        String msg = "Unknown result type: " + r.getClass();
//        Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
//        throw new UnsupportedSyntaxException(msg);
//    }

//    @Override
//    public Result visit(Dispatcher main, IASTLiteralExpression node) {
//        ILocation loc = new CACSLLocation(node);
//        switch (node.getKind()) {
//            case IASTLiteralExpression.lk_string_literal:
//                int someIntValue = 0;
//                char[] chars = node.getValue();
//                assert chars[0] == '"';
//                assert chars[chars.length - 1] == '"';
//                for (int i = 1; i < chars.length; i++) {
//                    someIntValue += Integer.valueOf(chars[i]);
//                }
//                return new ResultExpression(new IntegerLiteral(loc,
//                        new InferredType(InferredType.Type.Integer),
//                        String.valueOf(someIntValue)),
//                        new HashMap<VariableDeclaration, CACSLLocation>(0));
//        }
//        return super.visit(main, node);
//    }

    /* Christian:
     * pointers should not be treated as in 2013 
     * 
    @Override
    public Result visit(Dispatcher main, IASTUnaryExpression node) {
        ResultExpression o = (ResultExpression) main
                .dispatch(node.getOperand());
        switch (node.getOperator()) {
            case IASTUnaryExpression.op_star:
                return o;
                // case IASTUnaryExpression.op_amper:
                // return o;
        }
        return super.visit(main, node);
    }
    */

//    @Override
//    public Result visit(Dispatcher main, IASTPointer node) {
//        return new ResultTypes(new PrimitiveType(new CACSLLocation(node),
//                new InferredType(Type.Integer), SFO.INT), false, false, null);
//    }

    // Matthias:
    // Commented out to obtain UnsupportedSyntax instead of crash in SV-COMP
    // @Override
    // public Result visit(Dispatcher main, IASTTypeIdExpression node) {
    // Location loc = new CACSLLocation(node);
    // switch (node.getOperator()) {
    // case IASTTypeIdExpression.op_sizeof:
    // // Workaround for SV-COMP. sizeof any type is 42
    // return new ResultExpression(new IntegerLiteral(loc,
    // new InferredType(InferredType.Type.Integer), "42"));
    // default:
    // return super.visit(main, node);
    // }
    // }

    // Matthias:
    // Commented out to obtain UnsupportedSyntax instead of crash in SV-COMP
    // @Override
    // public Result visit(Dispatcher main, IASTIdExpression node) {
    // CACSLLocation loc = new CACSLLocation(node);
    // String cId = node.getName().getRawSignature();
    // if (!symbolTable.containsKey(cId)) {
    // String tmpId = main.nameHandler.getTempVarUID();
    // ArrayList<Statement> stmt = new ArrayList<Statement>();
    // ArrayList<Declaration> decl = new ArrayList<Declaration>();
    // VarList[] vl = new VarList[] { new VarList(loc,
    // new String[] { tmpId }, new PrimitiveType(loc, SFO.INT)) };
    // decl.add(new VariableDeclaration(loc, new Attribute[0], vl));
    // return new ResultExpression(stmt, new IdentifierExpression(loc,
    // tmpId), decl);
    // }
    // return super.visit(main, node);
    // }

}