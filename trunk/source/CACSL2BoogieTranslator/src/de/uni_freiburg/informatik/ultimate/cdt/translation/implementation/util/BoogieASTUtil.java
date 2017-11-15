/*
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
/**
 * Class holding static util methods, to operate on the BoogieAST.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import java.util.ArrayList;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.boogie.ast.VariableLHS;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * @author Markus Lindenmann
 * @since 12.09.2012
 */
public class BoogieASTUtil {
    /**
     * Helper method, to get the left most identifier of a LeftHandSide.
     *
     * @param lhs
     *            the LHS to process.
     * @return the left most identifier.
     */
    public static String getLHSId(final LeftHandSide lhs) {
        LeftHandSide l = lhs;
        while (l instanceof ArrayLHS || l instanceof StructLHS) {
            if (l instanceof ArrayLHS) {
				l = ((ArrayLHS) l).getArray();
			} else if (l instanceof StructLHS) {
				l = ((StructLHS) l).getStruct();
			}
        }
        return ((VariableLHS) l).getIdentifier();
    }

    /**
     * Helper method, to get the left most identifier of a Expression.
     *
     * @param expr
     *            the Expression to process (It is assumed, that
     *            <code>expr</code> is instance of one class in
     *            <code>{IdentifierExpression, StructAccessExpression, ArrayAccessExpression}</code>
     *            .).
     * @return the left most identifier.
     */
    public static String getLeftMostId(final Expression expr) {
        assert expr instanceof IdentifierExpression
                || expr instanceof StructAccessExpression
                || expr instanceof ArrayAccessExpression;
        Expression e = expr;
        while (e instanceof ArrayAccessExpression
                || e instanceof StructAccessExpression) {
            if (e instanceof ArrayAccessExpression) {
				e = ((ArrayAccessExpression) e).getArray();
			} else if (e instanceof StructAccessExpression) {
				e = ((StructAccessExpression) e).getStruct();
			}
        }
        return ((IdentifierExpression) e).getIdentifier();
    }

    /**
     * Flattens a LeftHandSide into a String Array. I.e. all accessed
     * identifiers are listed.
     *
     * @param lhs
     *            the LeftHandSide to flatten.
     * @return the flattened LHS as an array.
     */
    public static String[] getLHSList(final LeftHandSide lhs) {
        LeftHandSide l = lhs;
        final ArrayList<String> lhsList = new ArrayList<String>();
        while (l instanceof ArrayLHS || l instanceof StructLHS) {
            if (l instanceof ArrayLHS) {
                l = ((ArrayLHS) l).getArray();
            } else if (l instanceof StructLHS) {
                final StructLHS slhs = (StructLHS) l;
                lhsList.add(slhs.getField());
                l = slhs.getStruct();
            }
        }
        lhsList.add(((VariableLHS) l).getIdentifier());
        Collections.reverse(lhsList);
        return lhsList.toArray(new String[lhsList.size()]);
    }

    /**
     * Creates a LeftHandSide object for a given expression.
     *
     * @param e
     *            the expression to convert. It is assumed, that <code>e</code>
     *            is instance of one class in
     *            <code>{IdentifierExpression, StructAccessExpression, ArrayAccessExpression}</code>
     *            .
     * @return the created LHS object.
     */
    public static LeftHandSide getLHSforExpression(final Expression e) {
        assert e instanceof IdentifierExpression
                || e instanceof StructAccessExpression
                || e instanceof ArrayAccessExpression;
        final ILocation loc = e.getLocation();
        if (e instanceof IdentifierExpression) {
            final IdentifierExpression ie = (IdentifierExpression) e;
            return new VariableLHS(loc, ie.getType(), ie.getIdentifier(), null);
        }
        if (e instanceof StructAccessExpression) {
            final StructAccessExpression sae = (StructAccessExpression) e;
            final LeftHandSide lhs = getLHSforExpression(sae.getStruct());
            return new StructLHS(loc, sae.getType(), lhs, sae.getField());
        }
        if (e instanceof ArrayAccessExpression) {
            final ArrayAccessExpression aae = (ArrayAccessExpression) e;
            final LeftHandSide lhs = getLHSforExpression(aae.getArray());
            return ExpressionFactory.constructArrayLHS(loc, aae.getType(), lhs, aae.getIndices());
        }
        throw new IllegalArgumentException(
                "Wrong implementation! This method is not intended to handle this argument!");
    }
}
