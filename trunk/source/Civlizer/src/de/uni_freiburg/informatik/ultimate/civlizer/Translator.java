
package de.uni_freiburg.informatik.ultimate.civlizer;

import java.util.Arrays;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.boogie.ast.*;

public final class Translator extends GeneratedBoogieAstVisitor {

    private int mStmtCounter;
    private StringBuilder mResult;

    private Translator() {
        super();
        mResult = new StringBuilder("\n");
    }

    private void resetStmtCounter() {
        mStmtCounter = 0;
    }

    public static String translate(Unit boogieFile) {
        Translator translation = new Translator();

        boogieFile.accept(translation);

        return translation.toString();
    }

    @Override
    public String toString() {
        return mResult.toString();
    }

    public boolean visit(NamedAttribute node) {
        return true;
    }

    public boolean visit(StructType node) {
        return true;
    }

    public boolean visit(LeftHandSide node) {
        return true;
    }

    public boolean visit(FunctionApplication node) {
        return true;
    }

    public boolean visit(Label node) {
        return true;
    }

    public boolean visit(Unit node) {
        return true;
    }

    public boolean visit(VarList node) {
        return true;
    }

    public boolean visit(ArrayType node) {
        return true;
    }

    public boolean visit(IfStatement node) {
        return true;
    }

    public boolean visit(ParentEdge node) {
        return true;
    }

    public boolean visit(Trigger node) {
        return true;
    }

    public boolean visit(BinaryExpression node) {
        return true;
    }

    public boolean visit(AssignmentStatement node) {
        return true;
    }

    public boolean visit(LoopInvariantSpecification node) {
        return true;
    }

    public boolean visit(ReturnStatement node) {
        return true;
    }

    public boolean visit(Procedure node) {
        if (node.getIdentifier() == "ULTIMATE.start") {
            mResult.append("yield procedure {:layer 1} main({:linear} main_tid : MainTid) {\n")
                .append("// body TODO\n")
                .append("}\n\n");
        }
        else {
            mResult.append("yield procedure {:layer 1} ")
                .append(node.getIdentifier())
                .append("() {\n")
                .append("// body TODO\n")
                .append("}\n\n");
        }
        
        return false;
    }

    public boolean visit(PrimitiveType node) {
        return true;
    }

    public boolean visit(WildcardExpression node) {
        return true;
    }

    public boolean visit(Axiom node) {
        return true;
    }

    public boolean visit(IntegerLiteral node) {
        return true;
    }

    public boolean visit(EnsuresSpecification node) {
        return true;
    }

    public boolean visit(StructAccessExpression node) {
        return true;
    }

    public boolean visit(ForkStatement node) {
        // TODO ID ARG
        mResult.append("call fork_")
            .append(node.getProcedureName())
            .append(";\n\n");

        return false;
    }

    public boolean visit(CallStatement node) {
        // TODO ERROR 

        return false;
    }

    public boolean visit(JoinStatement node) {
        // TODO LHS ID
        mResult.append("call ID := join;\n\n");

        return false;
    }

    public boolean visit(VariableLHS node) {
        return true;
    }

    public boolean visit(Project node) {
        return true;
    }

    public boolean visit(ArrayStoreExpression node) {
        return true;
    }

    public boolean visit(StringLiteral node) {
        return true;
    }

    public boolean visit(ArrayLHS node) {
        return true;
    }

    public boolean visit(AssertStatement node) {
        return true;
    }

    public boolean visit(ModifiesSpecification node) {
        return true;
    }

    public boolean visit(RequiresSpecification node) {
        return true;
    }

    public boolean visit(Attribute node) {
        return true;
    }

    public boolean visit(NamedType node) {
        return true;
    }

    public boolean visit(BooleanLiteral node) {
        return true;
    }

    public boolean visit(UnaryExpression node) {
        return true;
    }

    public boolean visit(QuantifierExpression node) {
        return true;
    }

    public boolean visit(WhileStatement node) {
        return true;
    }

    public boolean visit(StructLHS node) {
        return true;
    }

    @Override
    public boolean visit(ConstDeclaration node) {
        // TODO handle attributes
        // improve var stream

        Stream<String> declaration_stream = Arrays.stream(node.getVarList().getIdentifiers());

        if (node.isUnique()) {
            declaration_stream.forEach(
                c -> mResult.append("const unique ").append(c).append(";\n\n")
            );
        }

        declaration_stream.forEach(
            c -> mResult.append("const ").append(c).append(";\n\n")
        );

        return true;
    }

    public boolean visit(FunctionDeclaration node) {
        // TODO

        return true;
    }

    public boolean visit(RealLiteral node) {
        return true;
    }

    public boolean visit(GotoStatement node) {
        return true;
    }

    @Override
    public boolean visit(VariableDeclaration node) {
        // TODO type whereClause

        for (VarList varl : node.getVariables()) {

            int len = varl.getIdentifiers().length;
            mResult.append("var {:layer 1,0} ");

            for (int i = 0; i < len - 1; i++) {
                mResult.append(varl.getIdentifiers()[i]).append(", ");
            }

            mResult.append(varl.getIdentifiers()[len - 1]).append(";\n\n");
        }

        return false;
    }
    
    @Override
    public boolean visit(Body node) {
        // TODO

        return false;
    }

    @Override
    public boolean visit(StructConstructor node) {
        // TODO 

        return false;
    }

    public boolean visit(AtomicStatement node) {
        return true;
    }

    public boolean visit(ASTType node) {
        return true;
    }

    public boolean visit(BitvecLiteral node) {
        return true;
    }

    public boolean visit(AssumeStatement node) {
        return true;
    }

    public boolean visit(Statement node) {
        return true;
    }

    public boolean visit(Specification node) {
        return true;
    }

    public boolean visit(IfThenElseExpression node) {
        return true;
    }

    public boolean visit(IdentifierExpression node) {
        return true;
    }

    public boolean visit(BreakStatement node) {
        return true;
    }

    public boolean visit(Expression node) {
        return true;
    }

    public boolean visit(BitVectorAccessExpression node) {
        return true;
    }

    @Override
    public boolean visit(TypeDeclaration node) {
        // TODO handle attributes

        if (node.isFinite()) {
            mResult.append("type finite ")
                .append(node.getIdentifier())
                .append(";\n\n");
        }
        else {
            mResult.append("type ")
                .append(node.getIdentifier())
                .append(";\n\n");
        }

        return false;
    }

    public boolean visit(ArrayAccessExpression node) {
        return true;
    }

    public boolean visit(HavocStatement node) {
        return true;
    }
}