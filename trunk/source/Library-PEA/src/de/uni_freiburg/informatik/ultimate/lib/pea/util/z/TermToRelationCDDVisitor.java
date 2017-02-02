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

package de.uni_freiburg.informatik.ultimate.lib.pea.util.z;

import java.io.StringWriter;

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import de.uni_freiburg.informatik.ultimate.lib.pea.RelationDecision;
import de.uni_freiburg.informatik.ultimate.lib.pea.RelationDecision.Operator;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.oz.util.Factory;
import net.sourceforge.czt.print.oz.PrintUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.ExistsPred;
import net.sourceforge.czt.z.ast.ForallExpr;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.ExistsExprVisitor;
import net.sourceforge.czt.z.visitor.ExistsPredVisitor;
import net.sourceforge.czt.z.visitor.ForallExprVisitor;
import net.sourceforge.czt.z.visitor.ForallPredVisitor;

/**
 * TermToBooleanCDDVisitor is a TermToCDDVisitor for the use of BooleanDecisions
 * instead of ZDecisions.
 *
 * @author jfaber
 *
 */
public class TermToRelationCDDVisitor extends TermToCDDVisitor
    implements ForallExprVisitor<CDD>, ForallPredVisitor<CDD>,
        ExistsExprVisitor<CDD>, ExistsPredVisitor<CDD>{

    /**
     * In CZT Z operators are always represented as " _ blubb _ ". This constant represents EQUAL.
     */
    private static final String Z_EQUALS_OPERATOR = ZString.ARG_TOK + ZString.EQUALS + ZString.ARG_TOK;
    private static final String Z_NEQ_OPERATOR = ZString.ARG_TOK + ZString.NEQ + ZString.ARG_TOK;
    @SuppressWarnings("unused")
    private static final String Z_LESS_OPERATOR = ZString.ARG_TOK + ZString.LESS+ ZString.ARG_TOK;
    @SuppressWarnings("unused")
    private static final String Z_LEQ_OPERATOR = ZString.ARG_TOK + ZString.LEQ + ZString.ARG_TOK;
    @SuppressWarnings("unused")
    private static final String Z_GREATER_OPERATOR = ZString.ARG_TOK + ZString.GREATER + ZString.ARG_TOK;
    @SuppressWarnings("unused")
    private static final String Z_GEQ_OPERATOR = ZString.ARG_TOK + ZString.GEQ + ZString.ARG_TOK;
    
    Factory factory = new Factory();
    
    /**
     * @param term
     *          A ZTerm which SectionInfo can be used to translate the term
     *          object back into unicode.
     */
    public TermToRelationCDDVisitor(ZTerm term) {
        super(term);
    }

    /* (non-Javadoc)
     * @see pea.util.z.TermToCDDVisitor#visitMemPred(net.sourceforge.czt.z.ast.MemPred)
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

    /* (non-Javadoc)
     * @see pea.util.z.TermToCDDVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
     */
    @Override
    public CDD visitTerm(Term zedObject) {
        final StringWriter sw = new StringWriter();
        PrintUtils.print(zedObject, sw, (SectionManager) sectionInfo,
                ZWrapper.getSectionName(), Markup.UNICODE);
        String result = sw.toString();
        result = result.replace(ZString.PRIME, Operator.PRIME.toString());
        result = result.replace(ZString.MINUS, Operator.MINUS.toString());
        result = result.replace(ZString.MULT, Operator.MULT.toString());
        /* "div" is defined in de.syspect.ozdcutils.symbols.ZArithmetic.INTEGER_DEVISION
         * but we do not want a dependency to SyspectDCOZUtil here.
         */
        result = result.replace(" div ", Operator.DIV.toString());
        result = result.replace(" ", "");
        
        try{
            if(result.contains(ZString.GEQ)){
                return getRelationDecFor(result.split(ZString.GEQ),Operator.GEQ);
            }else if(result.contains(ZString.LEQ)){
                return getRelationDecFor(result.split(ZString.LEQ),Operator.LEQ);
            }else if(result.contains(ZString.LESS)){
                return getRelationDecFor(result.split(ZString.LESS),Operator.LESS);
            }else if(result.contains(ZString.GREATER)){
                return getRelationDecFor(result.split(ZString.GREATER),Operator.GREATER);
            }else if(result.contains(ZString.NEQ)){
                return getRelationDecFor(result.split(ZString.NEQ),Operator.NEQ);
            }else if(result.contains(ZString.EQUALS)){
                return getRelationDecFor(result.split(ZString.EQUALS),Operator.EQUALS);
            }
        }catch (final IllegalArgumentException e) {
            throw new IllegalArgumentException("Found wrong number of operands in "
                    + result);
        }
        
        
        throw new RuntimeException("Term cannot be transformed into RelationDecision: "
                + result);
    }

    /**
     * Returns a RelationDecision for the given operator and the given
     * expressions contained in the array exprs.
     * 
     * @param exprs
     *          Left and right expression for the given binary operator.
     *          Throws a IllegalArgumentException() when exprs has not exactly two
     *          entries.
     * @param op
     *          The binary operator for the expression.
     * @return
     *          RelationDecision for the operator and the given expressions.
     */
    private CDD getRelationDecFor(String[] exprs, Operator op) {
        if(exprs.length != 2){
            throw new IllegalArgumentException();
        }
        return RelationDecision.create(exprs[0],op,exprs[1]);
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ForallExprVisitor#visitForallExpr(net.sourceforge.czt.z.ast.ForallExpr)
     */
    @Override
    public CDD visitForallExpr(ForallExpr arg0) {
        throw new TermNotSupportedException(arg0, sectionInfo);
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ForallPredVisitor#visitForallPred(net.sourceforge.czt.z.ast.ForallPred)
     */
    @Override
    public CDD visitForallPred(ForallPred arg0) {
        throw new TermNotSupportedException(arg0, sectionInfo);
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ExistsExprVisitor#visitExistsExpr(net.sourceforge.czt.z.ast.ExistsExpr)
     */
    @Override
    public CDD visitExistsExpr(ExistsExpr arg0) {
        throw new TermNotSupportedException(arg0, sectionInfo);
    }

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.ExistsPredVisitor#visitExistsPred(net.sourceforge.czt.z.ast.ExistsPred)
     */
    @Override
    public CDD visitExistsPred(ExistsPred arg0) {
        throw new TermNotSupportedException(arg0, sectionInfo);
    }

}
