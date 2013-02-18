/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base;

import java.util.HashSet;

import org.eclipse.cdt.core.dom.ast.ASTVisitor;
import org.eclipse.cdt.core.dom.ast.IASTArrayDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTArraySubscriptExpression;
import org.eclipse.cdt.core.dom.ast.IASTCompoundStatement;
import org.eclipse.cdt.core.dom.ast.IASTDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTDeclarator;
import org.eclipse.cdt.core.dom.ast.IASTExpression;
import org.eclipse.cdt.core.dom.ast.IASTFieldReference;
import org.eclipse.cdt.core.dom.ast.IASTForStatement;
import org.eclipse.cdt.core.dom.ast.IASTFunctionCallExpression;
import org.eclipse.cdt.core.dom.ast.IASTFunctionDefinition;
import org.eclipse.cdt.core.dom.ast.IASTIdExpression;
import org.eclipse.cdt.core.dom.ast.IASTNode;
import org.eclipse.cdt.core.dom.ast.IASTSimpleDeclaration;
import org.eclipse.cdt.core.dom.ast.IASTStatement;
import org.eclipse.cdt.core.dom.ast.IASTSwitchStatement;
import org.eclipse.cdt.core.dom.ast.IASTUnaryExpression;
import org.eclipse.cdt.internal.core.dom.parser.c.CASTSimpleDeclaration;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * @author Markus Lindenmann
 * @date 12.12.2012
 */
public class PreRunner extends ASTVisitor {
    /**
     * Variables, that have to go on the heap.
     */
    private HashSet<IASTDeclaration> variablesOnHeap;
    /**
     * The symbol table during the translation.
     */
    ScopedHashMap<String, IASTDeclaration> sT;
    /**
     * Whether or not the memory model is required.
     */
    private boolean isMMRequired;

    /**
     * Constructor.
     */
    public PreRunner() {
        this.shouldVisitDeclarations = true;
        this.shouldVisitExpressions = true;
        this.shouldVisitStatements = true;
        this.isMMRequired = false;
        this.sT = new ScopedHashMap<String, IASTDeclaration>();
        this.variablesOnHeap = new HashSet<IASTDeclaration>();
    }

    /**
     * Returns a set of variables, that have to be translated using the memory
     * model.
     * 
     * @return a set of variables, that have to be translated using the memory
     *         model.
     */
    public HashSet<IASTDeclaration> getVarsForHeap() {
        return variablesOnHeap;
    }

    /**
     * Whether the memory model is required or not.
     * 
     * @return true if the MM is required.
     */
    public boolean isMMRequired() {
        return this.isMMRequired;
    }

    @Override
    public int visit(IASTExpression expression) {
        if (expression instanceof IASTUnaryExpression) {
            ILocation loc = new CACSLLocation(expression);
            IASTUnaryExpression ue = (IASTUnaryExpression) expression;
            if (ue.getOperator() == IASTUnaryExpression.op_amper) {
                IASTNode operand = ue.getOperand();
                // add the operand to VariablesOnHeap!
                String n;
                if (operand instanceof IASTIdExpression) {
                    n = ue.getOperand().getRawSignature();
                } // TODO : add other cases! ie. structs, where the &-operator
                  // is applied to one field, etc
                else {
                    String m = "PR: Unsupported operand in UnarayExpression!";
                    Dispatcher.error(loc, SyntaxErrorType.UnsupportedSyntax, m);
                    throw new UnsupportedSyntaxException(m);
                }
                this.isMMRequired = true;
                this.variablesOnHeap.add(get(n, loc));
            } else if (!this.isMMRequired
                    && ue.getOperator() == IASTUnaryExpression.op_star) {
                this.isMMRequired = true;
            }
        }
        if (expression instanceof IASTIdExpression) {
            String n = expression.getRawSignature();
            IASTDeclaration d = sT.get(n); // don't check contains here!
            if (d instanceof IASTSimpleDeclaration) {
                if (((IASTSimpleDeclaration) d).getDeclarators()[0] instanceof IASTArrayDeclarator) {
                    if (!(expression.getParent() instanceof IASTArraySubscriptExpression)) {
                        // if idex is an array and there is no array sub expr!
                        this.variablesOnHeap.add(d);
                        this.isMMRequired = true;
                    }
                }
            }
        }
        if (expression instanceof IASTFieldReference) {
            // TODO
            // if field is an array and there is no array sub expr!
        }
        if (expression instanceof IASTFunctionCallExpression) {
            IASTFunctionCallExpression fce = (IASTFunctionCallExpression) expression;
            if (fce.getFunctionNameExpression().getRawSignature()
                    .equals("malloc")) {
                this.isMMRequired = true;
            } else if (fce.getFunctionNameExpression().getRawSignature()
                    .equals("free")) {
                this.isMMRequired = true;
            }
        }
        return super.visit(expression);
    }

    @Override
    public int visit(IASTDeclaration declaration) {
        if (declaration instanceof CASTSimpleDeclaration) {
            CASTSimpleDeclaration cd = (CASTSimpleDeclaration) declaration;
            for (IASTDeclarator d : cd.getDeclarators()) {
                String key = d.getName().getRawSignature();
                sT.put(key, declaration);
            }
        }
        if (declaration instanceof IASTFunctionDefinition) {
            sT.beginScope();
            int nr = super.visit(declaration);
            sT.endScope();
            return nr;
        }
        return super.visit(declaration);
    }

    @Override
    public int visit(IASTStatement statement) {
        if (statement instanceof IASTCompoundStatement
                && !(statement.getParent() instanceof IASTFunctionDefinition || statement
                        .getParent() instanceof IASTForStatement)) {
            // the scope for IASTFunctionDefinition and IASTForStatement was
            // opened in parent before!
            sT.beginScope();
            int nr = super.visit(statement);
            sT.endScope();
            return nr;
        }
        if (statement instanceof IASTSwitchStatement) {
            sT.beginScope();
            int nr = super.visit(statement);
            sT.endScope();
            return nr;
        }
        if (statement instanceof IASTForStatement) {
            sT.beginScope();
            int nr = super.visit(statement);
            sT.endScope();
            return nr;
        }
        return super.visit(statement);
    }

    /**
     * Getter to access the symbol table.
     * 
     * @param n
     *            the String name of the variable to retrieve from the symbol
     *            table.
     * @param l
     *            the location for the error, if the String is not contained.
     * @return the corresponding declaration for the given name.
     */
    private IASTDeclaration get(String n, ILocation l) {
        if (!sT.containsKey(n)) {
            String m = "PR: Missing declaration of " + n;
            Dispatcher.error(l, SyntaxErrorType.IncorrectSyntax, m);
            throw new IncorrectSyntaxException(m);
        }
        return sT.get(n);
    }
}
