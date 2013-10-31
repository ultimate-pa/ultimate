/**
 * Result for initializer lists. E.g. for arrays and structs.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.MemoryHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.StructHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.annotations.Overapprox;
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
     * @param lrVal
     *            the expression list to hold.
     * @param decl
     *            the declaration list to hold.
     */
    public ResultExpressionListRec(ArrayList<Statement> stmt, LRValue lrVal,
            ArrayList<Declaration> decl, 
            Map<VariableDeclaration, CACSLLocation> auxVars,
            List<Overapprox> overappr) {
        this(null, stmt, lrVal, decl, auxVars, overappr);
    }

    /**
     * Constructor.
     * 
     * @param field
     *            the name of the field e.g. in designated initializers.
     * @param stmt
     *            the statement list to hold.
     * @param lrVal
     *            the expression list to hold.
     * @param decl
     *            the declaration list to hold.
     */
    public ResultExpressionListRec(String field, ArrayList<Statement> stmt,
            LRValue lrVal, ArrayList<Declaration> decl, 
            Map<VariableDeclaration, CACSLLocation> auxVars,
            List<Overapprox> overappr) {
        super(stmt, lrVal, decl, auxVars, overappr);
        this.field = field;
        this.list = new ArrayList<ResultExpressionListRec>();
    }
    
    
    @Override
    public ResultExpressionListRec switchToRValue(Dispatcher main,
    		MemoryHandler memoryHandler, StructHandler structHandler,
    		ILocation loc) {
    	ResultExpression re = super.switchToRValue(main, memoryHandler, structHandler, loc);
    	
    	ArrayList<ResultExpressionListRec> newList = new ArrayList<ResultExpressionListRec>();
    	if (list != null) {
    		for (ResultExpressionListRec innerRerl : this.list) 
    			newList.add(innerRerl.switchToRValue(main, memoryHandler, structHandler, loc));
    	}
    	ResultExpressionListRec rerl = new ResultExpressionListRec(this.field,
    	        re.stmt, re.lrVal, re.decl, re.auxVars, re.overappr);
    	rerl.list.addAll(newList);
    	return rerl;
    }
}
