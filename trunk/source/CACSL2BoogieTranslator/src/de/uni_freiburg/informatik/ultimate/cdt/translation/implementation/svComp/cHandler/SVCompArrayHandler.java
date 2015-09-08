/*
 * Copyright (C) 2013-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
