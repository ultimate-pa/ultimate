/**
 * Result for initializer lists. E.g. for arrays and structs.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableDeclaration;

/**
 * @author Markus Lindenmann
 * @date 04.08.2012
 */
public class ResultExpressionListRec extends ResultExpression {
    /**
     * The list holding the single elements.
     */
    public final ArrayList<ResultExpressionListRec> list;
    /**
     * The name of this field, for designated initializers.
     */
    public final String field;

    /**
     * Constructor.
     */
    public ResultExpressionListRec() {
        this(null);
    }

    /**
     * Constructor.
     * 
     * @param field
     *            the name of the field e.g. in designated initializers.
     */
    public ResultExpressionListRec(String field) {
        super(null, new HashMap<VariableDeclaration, CACSLLocation>(0));
        this.field = field;
        this.list = new ArrayList<ResultExpressionListRec>();
    }

    /**
     * Constructor.
     * 
     * @param stmt
     *            the statement list to hold.
     * @param expr
     *            the expression list to hold.
     * @param decl
     *            the declaration list to hold.
     */
    public ResultExpressionListRec(ArrayList<Statement> stmt, Expression expr,
            ArrayList<Declaration> decl, 
            Map<VariableDeclaration, CACSLLocation> auxVars) {
        this(null, stmt, expr, decl, auxVars);
    }

    /**
     * Constructor.
     * 
     * @param field
     *            the name of the field e.g. in designated initializers.
     * @param stmt
     *            the statement list to hold.
     * @param expr
     *            the expression list to hold.
     * @param decl
     *            the declaration list to hold.
     */
    public ResultExpressionListRec(String field, ArrayList<Statement> stmt,
            Expression expr, ArrayList<Declaration> decl, 
            Map<VariableDeclaration, CACSLLocation> auxVars) {
        super(stmt, expr, decl, auxVars);
        this.field = field;
        this.list = null;
    }
}
