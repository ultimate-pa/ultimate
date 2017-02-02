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

import de.uni_freiburg.informatik.ultimate.lib.pea.CDD;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ImpliesExpr;
import net.sourceforge.czt.z.ast.ImpliesPred;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.NegExpr;
import net.sourceforge.czt.z.ast.NegPred;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.OrPred;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.AndPredVisitor;
import net.sourceforge.czt.z.visitor.ImpliesExprVisitor;
import net.sourceforge.czt.z.visitor.ImpliesPredVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.NegExprVisitor;
import net.sourceforge.czt.z.visitor.NegPredVisitor;
import net.sourceforge.czt.z.visitor.OrExprVisitor;
import net.sourceforge.czt.z.visitor.OrPredVisitor;
import net.sourceforge.czt.z.visitor.TruePredVisitor;

/**
 * TermToCDDVisitor converts a Term object into a CDD representation. The methods splits
 * the formula at And, Or, Implies-Operators (if possible). It does not generate
 * the actual decisions for the CDDs. This has to be done in classes derived from
 * this abstract class.
 *  
 * Please don't call the visitXXX-methods directly and
 * use the accept(Visitor<R> visitor)-Methods of the 
 * Term objects instead.
 * 
 * @see TermToZCDDVisitor
 * 
 * @author jfaber
 */
public abstract class TermToCDDVisitor  implements
    TermVisitor<CDD>,
    AndExprVisitor<CDD>,
    AndPredVisitor<CDD>,
    OrExprVisitor<CDD>,
    OrPredVisitor<CDD>,
    ImpliesExprVisitor<CDD>,
    ImpliesPredVisitor<CDD>,
    NegExprVisitor<CDD>,
    NegPredVisitor<CDD>,
    MemPredVisitor<CDD>,
    TruePredVisitor<CDD> {


    protected SectionInfo sectionInfo;

    @Override
	public abstract CDD visitMemPred(MemPred pred);

    @Override
	public abstract CDD visitTerm(Term zedObject);

    /**
     * @param term
     */
    public TermToCDDVisitor(ZTerm term) {
        sectionInfo = term.sectionInfo;
    }

    @Override
	public CDD visitAndExpr(AndExpr term) {
        CDD result = CDD.TRUE;
        for (final Expr expr : term.getExpr()) {
            result = result.and(expr.accept(this));
        }
        return result;
    }

    @Override
	public CDD visitAndPred(AndPred term) {
        CDD result = CDD.TRUE;
        for (final Pred pred : term.getPred()) {
            result = result.and(pred.accept(this));
        }
        return result;
    }

    @Override
    public CDD visitOrExpr(OrExpr term) {
        CDD result = CDD.FALSE;
        for (final Expr expr : term.getExpr()) {
            result = result.or(expr.accept(this));
        }
        return result;
    }

    @Override
    public CDD visitOrPred(OrPred term) {
        CDD result = CDD.FALSE;
        for (final Pred pred : term.getPred()) {
            result = result.or(pred.accept(this));
        }
        return result;
    }

    @Override
    public CDD visitImpliesExpr(ImpliesExpr term) {
        CDD result = term.getRightExpr().accept(this);
        result = result.or(term.getLeftExpr().accept(this).negate());
        return result;
    }

    @Override
    public CDD visitImpliesPred(ImpliesPred term) {
        CDD result = term.getRightPred().accept(this);
        result = result.or(term.getLeftPred().accept(this).negate());
        return result;
    }

    @Override
    public CDD visitNegExpr(NegExpr expr) {
        return expr.accept(this).negate();
    }

    @Override
    public CDD visitNegPred(NegPred pred) {
        return pred.getPred().accept(this).negate();
    }
    
    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.TruePredVisitor#visitTruePred(net.sourceforge.czt.z.ast.TruePred)
     */
    @Override
    public CDD visitTruePred(TruePred arg0) {
        return CDD.TRUE;
    }

}