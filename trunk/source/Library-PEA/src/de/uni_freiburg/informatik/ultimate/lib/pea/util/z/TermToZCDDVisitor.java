/* $Id$ 
 *
 * This file is part of the PEA toolkit (and Syspect)
 *
 * Syspect is a graphical development environment to create UML models 
 * specifying a system and converting this specification into 
 * various formats including CSP-OZ-DC.
 * 
 * Copyright (C) 2007, Carl von Ossietzky University of Oldenburg
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
package de.uni_freiburg.informatik.ultimate.lib.pea.util.z;

import java.io.StringWriter;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.ZDecision;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.oz.util.Factory;
import net.sourceforge.czt.print.oz.PrintUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZString;

/**
 * TermToCDDVisitor converts a Term object into a CDD representation using ZDecisions. The methods splits
 * the formula at And, Or, Implies-Operators (if possible) and handles the remaining terms as new ZDecisions.
 * 
 * Please don't call the visitXXX-methods directly and
 * use the accept(Visitor<R> visitor)-Methods of the 
 * Term objects instead.
 * 
 * @author jfaber
 *
 */
public class TermToZCDDVisitor extends TermToCDDVisitor {

    /**
     * In CZT Z operators are always represented as " _ blubb _ ". This constant represents EQUAL.
     */
    private static final String Z_EQUALS_OPERATOR = ZString.ARG_TOK + ZString.EQUALS + ZString.ARG_TOK;
    
    /**
     * In CZT Z operators are always represented as " _ blubb _ ". This constant represents NEQ.
     */
    private static final String Z_NEQ_OPERATOR = ZString.ARG_TOK + ZString.NEQ + ZString.ARG_TOK;
    
    Factory factory = new Factory();
    
    /**
     * @param term
     *          A ZTerm which SectionInfo can be used to translate the term
     *          object back into unicode.
     */
    public TermToZCDDVisitor(ZTerm term) {
        super(term);
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.base.visitor.TermVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
     */
    @Override
    public CDD visitTerm(Term zedObject) {
        final StringWriter sw = new StringWriter();
        PrintUtils.print(zedObject, sw, (SectionManager) sectionInfo,
                ZWrapper.getSectionName(), Markup.UNICODE);
        return ZDecision.create(sw.toString());
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.MemPredVisitor#visitMemPred(net.sourceforge.czt.z.ast.MemPred)
     */
    @Override
    public CDD visitMemPred(MemPred pred) {
        if(pred.getRightExpr() instanceof RefExpr) {
            final RefExpr refExpr = (RefExpr)pred.getRightExpr();
            final ZName name = refExpr.getZName();
            // We replace expressions like a != b + c with NOT(a = b + c)
            if(name.getOperatorName().getWord().equals(Z_NEQ_OPERATOR)) {
                final ZName newRefName = factory.createZName(
                        Z_EQUALS_OPERATOR,
                        name.getStrokeList());
                final RefExpr newRefExpr = 
                    factory.createRefExpr(newRefName, refExpr.getZExprList(), refExpr.getMixfix());
                final Pred newMemPred = factory.createMemPred(pred.getLeftExpr(), newRefExpr, pred.getMixfix());
                return newMemPred.accept(this).negate();
            }
        }
        return visitTerm(pred);
    }



}
