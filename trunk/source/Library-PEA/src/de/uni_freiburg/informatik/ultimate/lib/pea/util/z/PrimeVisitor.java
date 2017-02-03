/* $$Id: PrimeReferencedVariablesVisitor.java 5597 2008-03-14 10:29:49Z jfaber $$ 
 *
 * This file is part of Syspect
 *
 * Syspect is a graphical development environment to create UML models 
 * specifying a system and converting this specification into 
 * various formats including CSP-OZ-DC.
 * 
 * Copyright (C) ${year}, Carl von Ossietzky University of Oldenburg
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

import java.util.HashSet;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.oz.util.Factory;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.QntPred;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.visitor.QntPredVisitor;
import net.sourceforge.czt.z.visitor.ZNameVisitor;

/**
 * PrimeVisitor is a Object-Z-Term-Visitor,
 * which searches all undecorated variables of the given
 * term and adds a 'next' stroke to them (primes them).
 * 
 * 
 * @author cthulhu, jfaber
 */
public class PrimeVisitor implements TermVisitor,
		ZNameVisitor,
		QntPredVisitor {

	private final Factory factory;
	private final HashSet<String> bounded;

	public PrimeVisitor() {
		factory = new Factory();
		bounded = new HashSet<String>();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see net.sourceforge.czt.base.visitor.TermVisitor#visitTerm(net.sourceforge.czt.base.ast.Term)
	 */
	@Override
	@SuppressWarnings("unchecked")
	public Object visitTerm(Term zedObject) {
		final Object[] children = zedObject.getChildren();
		for (final Object child : children) {
			if (child instanceof Term) {
				((Term) child).accept(this);
			}
		}
		return null;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see net.sourceforge.czt.z.visitor.ZNameVisitor#visitZName(net.sourceforge.czt.z.ast.ZName)
	 */
	@Override
	public Object visitZName(ZName term) {
		if (term.getOperatorName() == null && 
		        !bounded.contains(term.getWord()) &&
		        term.getZStrokeList().isEmpty()) {
			term.getZStrokeList().add(factory.createNextStroke());
		}
		return null;
	}

    /* (non-Javadoc)
     * @see net.sourceforge.czt.z.visitor.QntPredVisitor#visitQntPred(net.sourceforge.czt.z.ast.QntPred)
     */
    @SuppressWarnings("unchecked")
    @Override
    public Object visitQntPred(QntPred pred) {
        final HashSet<String> newBounded = new HashSet<String>();
        for (final Decl decl : pred.getZSchText().getZDeclList()) {
            if(decl instanceof VarDecl) {
                for (final Name name : ((VarDecl)decl).getZNameList()) {
                    if(name instanceof ZName &&
                            !bounded.contains(name)) {
                        newBounded.add(((ZName)name).getWord());
                    }
                }
            }
        }
        bounded.addAll(newBounded);
        if(pred.getZSchText().getPred() != null) {
			pred.getZSchText().getPred().accept(this);
		}
        pred.getPred().accept(this);
        bounded.removeAll(newBounded);
        return null;
    }

}
