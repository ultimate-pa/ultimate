/**
 * An example for a ACSL handler implementation.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Stack;

import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTNode;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.SymbolTableValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.TypeErrorException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.HeapLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LRValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.LocalLValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultContract;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.BoogieASTUtil;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.handler.IACSLHandler;
import de.uni_freiburg.informatik.ultimate.model.IType;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.acsl.ACSLNode;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assertion;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Assigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.CodeAnnotStmt;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Contract;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ContractStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Ensures;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FieldAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.FreeableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAnnot;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopAssigns;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopInvariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopStatement;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.LoopVariant;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.MallocableExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.Requires;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ResultExpression;
import de.uni_freiburg.informatik.ultimate.model.acsl.ast.ValidExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ASTType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.EnsuresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LoopInvariantSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ModifiesSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RequiresSpecification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Specification;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VarList;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @date 28.02.2012
 */
public class ACSLHandler implements IACSLHandler {

    /**
     * To determine the right names, we need to know where we are in the
     * specification.
     */
    private enum SPEC_TYPE {
        /**
         * Not specified.
         */
        NOT,
        /**
         * ACSL requires statement.
         */
        REQUIRES,
        /**
         * ACSL assigns statement.
         */
        ASSIGNS,
        /**
         * ACSL ensures statement.
         */
        ENSURES
    }

    /**
     * Holds the spec type, which we need later in the code.
     */
    private ACSLHandler.SPEC_TYPE specType = ACSLHandler.SPEC_TYPE.NOT;

    /**
     * @deprecated is not supported in this handler! Do not use!
     */
    @Override
    public Result visit(Dispatcher main, IASTNode node) {
        throw new UnsupportedOperationException(
                "Implementation Error: Use CHandler for: " + node.getClass());
    }

    @Override
    public Result visit(Dispatcher main, ACSLNode node) {
        String msg = "ACSLHandler: Not yet implemented: " + node.toString();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    @Override
    public Result visit(Dispatcher main, CodeAnnot node) {
        if (node instanceof CodeAnnotStmt) {
            Result formula = main.dispatch(((Assertion) ((CodeAnnotStmt) node)
                    .getCodeStmt()).getFormula());
            return new Result(new AssertStatement(new CACSLLocation(node,
                    new Check(Check.Spec.ASSERT)), ((Expression) formula.node)));
        }
        // TODO : other cases
        String msg = "ACSLHandler: Not yet implemented: " + node.toString();
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.UnsupportedSyntax, msg);
        throw new UnsupportedSyntaxException(msg);
    }

    /**
     * Translates an ACSL binary expression operator into a boogie binary
     * expression operator, iff there is a one to one translation - otherwise
     * null.
     * 
     * @param op
     *            the ACSL binary expression operator
     * @return the translates operator or null.
     */
    private static Operator getBoogieBinaryExprOperator(
            de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression.Operator op) {
        switch (op) {
            case ARITHDIV:
                return Operator.ARITHDIV;
            case ARITHMINUS:
                return Operator.ARITHMINUS;
            case ARITHMOD:
                return Operator.ARITHMOD;
            case ARITHMUL:
                return Operator.ARITHMUL;
            case ARITHPLUS:
                return Operator.ARITHPLUS;
            case BITVECCONCAT:
                return Operator.BITVECCONCAT;
            case COMPEQ:
                return Operator.COMPEQ;
            case COMPGEQ:
                return Operator.COMPGEQ;
            case COMPGT:
                return Operator.COMPGT;
            case COMPLEQ:
                return Operator.COMPLEQ;
            case COMPLT:
                return Operator.COMPLT;
            case COMPNEQ:
                return Operator.COMPNEQ;
            case COMPPO:
                return Operator.COMPPO;
            case LOGICAND:
                return Operator.LOGICAND;
            case LOGICIFF:
                return Operator.LOGICIFF;
            case LOGICIMPLIES:
                return Operator.LOGICIMPLIES;
            case LOGICOR:
                return Operator.LOGICOR;
            case BITXOR:
            case BITAND:
            case BITIFF:
            case BITIMPLIES:
            case BITOR:
            case LOGICXOR:
            default:
                return null;
        }
    }

    @Override
    public Result visit(
            Dispatcher main,
            de.uni_freiburg.informatik.ultimate.model.acsl.ast.BinaryExpression node) {
        ILocation loc = new CACSLLocation(node);
        Expression left = (Expression) main.dispatch(node.getLeft()).node;
        Expression right = (Expression) main.dispatch(node.getRight()).node;
        if (left.getType() != null) {
            right = main.typeHandler.convertArith2Boolean(loc,
                    new PrimitiveType(loc, left.getType(), left.getType()
                            .toString()), right);
        }
        Operator op = getBoogieBinaryExprOperator(node.getOperator());
        if (op != null) {
            return new Result(new BinaryExpression(loc, op, left, right));
        }
        switch (node.getOperator()) {
            case LOGICXOR:
                // translate into (l | r)
                // where l = left & !right
                UnaryExpression notRight = new UnaryExpression(loc,
                        UnaryExpression.Operator.LOGICNEG, right);
                BinaryExpression l = new BinaryExpression(loc,
                        Operator.LOGICAND, left, notRight);
                // and r = !left & right
                UnaryExpression notLeft = new UnaryExpression(loc,
                        UnaryExpression.Operator.LOGICNEG, left);
                BinaryExpression r = new BinaryExpression(loc,
                        Operator.LOGICAND, notLeft, right);
                return new Result(new BinaryExpression(loc, Operator.LOGICOR,
                        l, r));
            case BITAND:
            case BITIFF:
            case BITIMPLIES:
            case BITOR:
            case BITXOR:
            default:
                String msg = "Unknown or unsupported binary operation: "
                        + node.getOperator();
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
    }

    @Override
    public Result visit(
            Dispatcher main,
            de.uni_freiburg.informatik.ultimate.model.acsl.ast.UnaryExpression node) {
        ILocation loc = new CACSLLocation(node);
        Expression expr = (Expression) main.dispatch(node.getExpr()).node;
        switch (node.getOperator()) {
            case LOGICNEG:
                return new Result(new UnaryExpression(loc,
                        UnaryExpression.Operator.LOGICNEG, expr));
            case MINUS:
                return new Result(new UnaryExpression(loc,
                        UnaryExpression.Operator.ARITHNEGATIVE, expr));
            case PLUS:
                return new Result(expr);
            case POINTER:
            case ADDROF:
            case LOGICCOMPLEMENT:
            default:
                String msg = "Unknown or unsupported unary operation: "
                        + node.getOperator();
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
                throw new UnsupportedSyntaxException(msg);
        }
    }

    @Override
    public Result visit(Dispatcher main, IntegerLiteral node) {
        return new Result(
                new de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral(
                        new CACSLLocation(node), node.getValue()));
    }

    @Override
    public Result visit(Dispatcher main, BooleanLiteral node) {
        return new Result(
                new de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral(
                        new CACSLLocation(node), node.getValue()));
    }

    @Override
    public Result visit(Dispatcher main, RealLiteral node) {
        return new Result(
                new de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral(
                        new CACSLLocation(node), node.getValue()));
    }

    @Override
    public Result visit(
            Dispatcher main,
            de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression node) {
        String id = SFO.EMPTY;
        CACSLLocation loc = new CACSLLocation(node);
        switch (specType) {
            case ASSIGNS:
                // modifies case in boogie, should be always global!
                // maybe it is allowed to assign also in parameters?
                // Global variable
                id = node.getIdentifier();
                SymbolTableValue stv = main.cHandler.getSymbolTable().get(id,
                        loc);
                if (stv.isGlobalVar()) {
                    id = stv.getBoogieName();
                } else {
                    String msg = "It is not allowed to assign to in parameters! Should be global variables! ["
                            + node.getIdentifier() + "]";
                    Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
                    throw new IncorrectSyntaxException(msg);
                }
                break;
            case ENSURES:
                if (node.getIdentifier().equalsIgnoreCase("\result")) {
                    id = SFO.RES;
                } else {
                	id = node.getIdentifier();
                    stv = main.cHandler.getSymbolTable().get(id, loc);
                    id = stv.getBoogieName();
                }
                break;
            case REQUIRES:
            	id = node.getIdentifier();
                stv = main.cHandler.getSymbolTable().get(id, loc);
                id = stv.getBoogieName();
                break;
            case NOT:
                // We to handle the scope, so that we address here the right
                // variable
                String cId = node.getIdentifier();
                id = main.cHandler.getSymbolTable().get(cId, loc)
                        .getBoogieName();
                break;
            default:
                String msg = "The type of specType should be in some type!";
                Dispatcher.error(loc, SyntaxErrorType.TypeError, msg);
                throw new TypeErrorException(msg);
        }
        
        
        IType type = new InferredType(InferredType.Type.Unknown);
        String cId = main.cHandler.getSymbolTable()
                    .getCID4BoogieID(id, loc);
        if (specType != ACSLHandler.SPEC_TYPE.REQUIRES
                && specType != ACSLHandler.SPEC_TYPE.ENSURES) {
            // TODO : the translation is sometimes wrong, for requires and
            // ensures! i.e. when referring to inparams in ensures clauses!
            // The ensures clause will refer to the in-parameter listed in the
            // in parameter declaration. However, these variables will not be
            // changed, but only assigned to #in~NAME!
            // This cannot be solved by just appending "#in~" to all
            // identifiers, since the identifier could also refer to a global
            // variable! However, we don't know that at this moment!

            if (main.cHandler.getSymbolTable().containsKey(cId)) {
                ASTType astt = main.cHandler.getSymbolTable()
                        .getTypeOfVariable(cId, loc);
                type = new InferredType(astt);
            }
        }
        
        //FIXME: dereferencing does not work for ACSL yet, because we cannot pass 
        // the necessary auxiliary statements on.
        LRValue lrVal;
        if (((CHandler) main.cHandler).isHeapVar(id)) {
            IdentifierExpression idExp = new IdentifierExpression(loc, type, id);
        	lrVal = new HeapLValue(idExp);
        } else {
            VariableLHS idLhs = new VariableLHS(loc, type, id);
        	lrVal = new LocalLValue(idLhs);
        }
        
        return new Result(lrVal.getValue());
    }

    @Override
    public Result visit(Dispatcher main, Contract node) {
        ILocation loc = new CACSLLocation(node);
        ArrayList<Specification> spec = new ArrayList<Specification>();
        // First we catch the case that a contract is at a FunctionDefinition
        if (node instanceof IASTFunctionDefinition) {
            String msg = "Syntax Error, Contracts on FunctionDefinition are not allowed";
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }

        for (ContractStatement stmt : node.getContractStmt()) {
            spec.addAll(Arrays.asList(((ResultContract) main.dispatch(stmt)).specs));
        }
        if (node.getBehaviors() != null && node.getBehaviors().length != 0) {
            String msg = "Not yet implemented: Behaviour";
            Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
            throw new UnsupportedSyntaxException(msg);
        }
        // TODO : node.getCompleteness();
        specType = ACSLHandler.SPEC_TYPE.NOT;
        return new ResultContract(spec.toArray(new Specification[0]));
    }

    @Override
    public Result visit(Dispatcher main, Requires node) {
        specType = ACSLHandler.SPEC_TYPE.REQUIRES;
        Expression formula = (Expression) main.dispatch(node.getFormula()).node;
        ILocation reqLoc = new CACSLLocation(node, new Check(
                Check.Spec.PRE_CONDITION));
        RequiresSpecification req = new RequiresSpecification(reqLoc, false,
                formula);
        return new ResultContract(new Specification[] { req });
    }

    @Override
    public Result visit(Dispatcher main, Ensures node) {
        CACSLLocation loc = new CACSLLocation(node);
        de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression e = node
                .getFormula();
        if (e instanceof FieldAccessExpression
                || e instanceof ArrayAccessExpression) {
            // variable declaration not yet translated, hence we cannot
            // translate this access expression!
            String msg = "Ensures specification on struct types is not supported!";
            Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
            throw new UnsupportedSyntaxException(msg);
        }
        specType = ACSLHandler.SPEC_TYPE.ENSURES;
        Expression formula = (Expression) main.dispatch(e).node;
        ILocation ensLoc = new CACSLLocation(node, new Check(
                Check.Spec.POST_CONDITION));
        EnsuresSpecification ens = new EnsuresSpecification(ensLoc, false,
                formula);
        return new ResultContract(new Specification[] { ens });
    }

    @Override
    public Result visit(Dispatcher main, Assigns node) {
        specType = ACSLHandler.SPEC_TYPE.ASSIGNS;
        ILocation loc = new CACSLLocation(node);
        ArrayList<String> identifiers = new ArrayList<String>();
        for (de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression e : node
                .getLocations()) {
            if (e instanceof de.uni_freiburg.informatik.ultimate.model.acsl.ast.IdentifierExpression) {
                identifiers.add(((IdentifierExpression) main.dispatch(e).node)
                        .getIdentifier());
            } else {
                Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax,
                        "Unexpected Expression: " + e.getClass());
                throw new UnsupportedSyntaxException("Unexpected Expression: "
                        + e.getClass());
            }
        }
        VariableLHS[] identifiersVarLHS = new VariableLHS[identifiers.size()];
        for (int i = 0; i < identifiers.size(); i++)
        	identifiersVarLHS[i] = new VariableLHS(loc, identifiers.get(i));
        	
        ModifiesSpecification req = new ModifiesSpecification(loc, false,
                identifiersVarLHS);
        return new ResultContract(new Specification[] { req });
    }

    @Override
    public Result visit(Dispatcher main, ResultExpression node) {
        return new Result(new IdentifierExpression(new CACSLLocation(node),
                "#res"));
    }

    @Override
    public Result visit(Dispatcher main, LoopAnnot node) {
        if (node.getLoopBehavior() != null
                && node.getLoopBehavior().length != 0) {
            Dispatcher.error(new CACSLLocation(node),
                    SyntaxErrorType.UnsupportedSyntax,
                    "Not yet implemented: Behaviour");
            throw new UnsupportedSyntaxException(
                    "Not yet implemented: Behaviour");
        }
        ArrayList<Specification> specs = new ArrayList<Specification>();
        for (LoopStatement lst : node.getLoopStmt()) {
            Result res = main.dispatch(lst);
            assert res != null && res.node != null;
            assert res.node instanceof Specification;
            specs.add((Specification) res.node);
        }
        return new ResultContract(specs.toArray(new Specification[0]));
    }

    @Override
    public Result visit(Dispatcher main, LoopInvariant node) {
        Result res = main.dispatch(node.getFormula());
        assert res != null && res.node != null;
        assert res.node instanceof Expression;
        ILocation invLoc = new CACSLLocation(node, new Check(
                Check.Spec.INVARIANT));
        LoopInvariantSpecification lis = new LoopInvariantSpecification(invLoc,
                false, (Expression) res.node);
        return new Result(lis);
    }

    @Override
    public Result visit(Dispatcher main, LoopVariant node) {
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.UnsupportedSyntax,
                "Not yet implemented: LoopVariant");
        throw new UnsupportedSyntaxException("Not yet implemented: LoopVariant");
    }

    @Override
    public Result visit(Dispatcher main, LoopAssigns node) {
        Dispatcher.error(new CACSLLocation(node),
                SyntaxErrorType.UnsupportedSyntax,
                "Not yet implemented: LoopAssigns");
        throw new UnsupportedSyntaxException("Not yet implemented: LoopAssigns");
    }

    @Override
    public Result visit(Dispatcher main, ArrayAccessExpression node) {
        CACSLLocation loc = new CACSLLocation(node);
        Stack<Expression> args = new Stack<Expression>();

        de.uni_freiburg.informatik.ultimate.model.acsl.ast.Expression arr = node;
        do {
            assert arr instanceof ArrayAccessExpression;
            assert ((ArrayAccessExpression) arr).getIndices().length == 1;
            Result arg = main.dispatch(((ArrayAccessExpression) arr)
                    .getIndices()[0]);
            assert arg.getClass() == Result.class;
            assert arg.node instanceof Expression;
            args.push((Expression) arg.node);
            arr = ((ArrayAccessExpression) arr).getArray();
        } while (arr instanceof ArrayAccessExpression);

        Expression[] idx = new Expression[args.size()];
        Collections.reverse(args);
        args.toArray(idx);
        Result idExprRes = main.dispatch(arr);
        assert idExprRes.getClass() == Result.class;
        assert idExprRes.node instanceof Expression;
        Expression subExpr = (Expression) idExprRes.node;

        de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression expr;
        if (subExpr instanceof IdentifierExpression) {
            IdentifierExpression idEx = (IdentifierExpression) subExpr;
            String bId = idEx.getIdentifier();
            String cId = main.cHandler.getSymbolTable().getCID4BoogieID(bId,
                    loc);
            assert main.cHandler.getSymbolTable().containsKey(cId);
            InferredType it = new InferredType(main.cHandler.getSymbolTable()
                    .getTypeOfVariable(cId, loc));
            expr = new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression(
                    loc, it, idEx, idx);
        } else if (subExpr instanceof StructAccessExpression) {
            StructAccessExpression sae = (StructAccessExpression) subExpr;
            StructLHS lhs = (StructLHS) BoogieASTUtil.getLHSforExpression(sae);
            ASTType t = main.typeHandler.getTypeOfStructLHS(
                    main.cHandler.getSymbolTable(), loc, lhs);
            if (!(t instanceof ArrayType)) {
                String msg = "Type mismatch - cannot take index on a not-array element!";
                Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
                throw new IncorrectSyntaxException(msg);
            }
            expr = new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression(
                    loc, sae.getType(), sae, idx);
        } else {
            String msg = "Unexpected result type on left side of array!";
            Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, msg);
            throw new UnsupportedSyntaxException(msg);
        }
        return new Result(expr);
    }

    @Override
    public Result visit(Dispatcher main, FieldAccessExpression node) {
        Result r = main.dispatch(node.getStruct());
        assert r.getClass() == Result.class;
        assert r.node instanceof Expression;
        String field = node.getField();
        return new Result(new StructAccessExpression(new CACSLLocation(node),
                (Expression) r.node, field));
    }

    @Override
    public Result visit(Dispatcher main, FreeableExpression node) {
        CACSLLocation loc = new CACSLLocation(node);
        IType it = new InferredType(InferredType.Type.Boolean);
        Result rIdc = main.dispatch(node.getFormula());
        Expression idx = (Expression) rIdc.node;
        idx = new StructAccessExpression(loc, idx, SFO.POINTER_BASE);
        Expression[] idc = new Expression[] { idx };
        Expression arr = new IdentifierExpression(loc, SFO.VALID);
        Expression e = new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression(
                loc, it, arr, idc);
        return new Result(e);

    }

    @Override
    public Result visit(Dispatcher main, MallocableExpression node) {
        CACSLLocation loc = new CACSLLocation(node);
        IType it = new InferredType(InferredType.Type.Boolean);
        Result rIdc = main.dispatch(node.getFormula());
        Expression idx = (Expression) rIdc.node;
        idx = new StructAccessExpression(loc, idx, SFO.POINTER_BASE);
        Expression[] idc = new Expression[] { idx };
        Expression arr = new IdentifierExpression(loc, SFO.VALID);
        Expression valid = new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression(
                loc, it, arr, idc);
        Expression e = new UnaryExpression(
                loc,
                it,
                de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression.Operator.LOGICNEG,
                valid);
        return new Result(e);
    }

    @Override
    public Result visit(Dispatcher main, ValidExpression node) {
        CACSLLocation loc = new CACSLLocation(node);
        IType it = new InferredType(InferredType.Type.Boolean);
        Result rIdc = main.dispatch(node.getFormula());
        Expression idx = (Expression) rIdc.node;
        idx = new StructAccessExpression(loc, idx, SFO.POINTER_BASE);
        Expression[] idc = new Expression[] { idx };
        Expression arr = new IdentifierExpression(loc, SFO.VALID);
        Expression e = new de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression(
                loc, it, arr, idc);
        return new Result(e);
    }
}
