package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.svComp.cHandler;

import java.util.ListIterator;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.ArrayHandler;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.Result;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.ResultExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Statement;

/**
 * @author Markus Lindenmann
 * @date 12.10.2012
 */
public class SVCompArrayHandler extends ArrayHandler {
//    @Override
//    public ResultExpression handleArrayInit(Dispatcher main, MemoryHandler memoryHandler,
//            StructHandler structHandler, CACSLLocation loc, ArrayType at,
//            CArray cvar, LeftHandSide lhs, ResultExpressionListRec relr,
//            int[] indices, int pos) {
//        return filterAsserts(super.handleArrayInit(main, memoryHandler, structHandler, loc,
//                at, cvar, lhs, relr, indices, pos));
//    }

//    @Override
//    public Result handleArraySubscriptionExpression(Dispatcher main, MemoryHandler memoryHandler,
//    		StructHandler structHandler, IASTArraySubscriptExpression node) {
//        return filterAsserts(super
//                .handleArraySubscriptionExpression(main, memoryHandler, structHandler, node));
//    }

    /**
     * Removes AssertStatements from this results Statement list.
     * 
     * @param r
     *            a result.
     * @return a filtered result.
     */
    private static ResultExpression filterAsserts(final Result r) {
        assert r instanceof ResultExpression;
        ResultExpression rex = (ResultExpression) r;
        for (ListIterator<Statement> iter = rex.stmt.listIterator(rex.stmt
                .size()); iter.hasPrevious();) {
            if (iter.previous() instanceof AssertStatement)
                iter.remove();
        }
        return rex;
    }
}
