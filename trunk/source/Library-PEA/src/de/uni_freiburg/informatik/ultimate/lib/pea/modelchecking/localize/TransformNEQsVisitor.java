/* $Id$ 
 *
 * This file is part of the PEA tool set
 * 
 * The PEA tool set is a collection of tools for Phase Event Automata
 * (PEA).
 * 
 * Copyright (C) 2005-2006, Carl von Ossietzky University of Oldenburg
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA
 */

package de.uni_freiburg.informatik.ultimate.lib.pea.modelchecking.localize;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.oz.util.Factory;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZString;

/**
 * TransformNEQsVisitor is a visitor for CZT term objects which returns a new
 * term object where every expression "a NEQ b" is transformed into "NEG (a EQUALS b)".
 * 
 * Currently not in use anymore!
 *
 * @author jfaber
 *
 */
public class TransformNEQsVisitor implements
    TermVisitor<Term> {

    /**
     * In CZT Z operators are always represented as " _ blubb _ ". This constant represents EQUAL.
     */
    private static final String Z_EQUALS_OPERATOR = ZString.ARG_TOK + ZString.EQUALS + ZString.ARG_TOK;
    
    /**
     * In CZT Z operators are always represented as " _ blubb _ ". This constant represents NEQ.
     */
    private static final String Z_NEQ_OPERATOR = ZString.ARG_TOK + ZString.NEQ + ZString.ARG_TOK;
    Factory factory = new Factory();
    
    /* (non-Javadoc)
     * @see net.sourceforge.czt.base.visitor.TermVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
     */
    @Override
    public Term visitTerm(Term zedObject) {
        final Object[] children = zedObject.getChildren();
        final Object[] newChildren = new Object[children.length];
        for (int i = 0; i < children.length; i++) {;
            final Object child = children[i];
            if( child instanceof MemPred) {
                final MemPred pred = (MemPred)child;
                if(pred.getRightExpr() instanceof RefExpr) {
                    final RefExpr refExpr = (RefExpr)pred.getRightExpr();
                    final ZName name = refExpr.getZName();
                    if(name.getOperatorName().getWord().equals(Z_NEQ_OPERATOR)) {
                        
                        final ZName newRefName = factory.createZName(
                                Z_EQUALS_OPERATOR,
                                name.getStrokeList());
                        final RefExpr newRefExpr = 
                            factory.createRefExpr(newRefName, refExpr.getZExprList(), refExpr.getMixfix());
                        final Pred newMemPred = factory.createMemPred(pred.getLeftExpr(), newRefExpr, pred.getMixfix());
                        
                        newChildren[i] = factory.createNegPred((Pred) newMemPred.accept(this));
                        continue;
                    }
                }
                newChildren[i] = ((Term) child).accept(this);
            }else if (child instanceof Term) {
                newChildren[i] = ((Term) child).accept(this);
            }else {
                newChildren[i] = children[i];
            }
        }
        return zedObject.create(newChildren);
    }

}
