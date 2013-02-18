/**
 * Class holding static util methods, to operate on the BoogieAST.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import java.util.ArrayList;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.model.ILocation;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.ArrayLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.LeftHandSide;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructAccessExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.StructLHS;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.VariableLHS;

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
            if (l instanceof ArrayLHS)
                l = ((ArrayLHS) l).getArray();
            else if (l instanceof StructLHS)
                l = ((StructLHS) l).getStruct();
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
            if (e instanceof ArrayAccessExpression)
                e = ((ArrayAccessExpression) e).getArray();
            else if (e instanceof StructAccessExpression)
                e = ((StructAccessExpression) e).getStruct();
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
        ArrayList<String> lhsList = new ArrayList<String>();
        while (l instanceof ArrayLHS || l instanceof StructLHS) {
            if (l instanceof ArrayLHS) {
                l = ((ArrayLHS) l).getArray();
            } else if (l instanceof StructLHS) {
                StructLHS slhs = (StructLHS) l;
                lhsList.add(slhs.getField());
                l = slhs.getStruct();
            }
        }
        lhsList.add(((VariableLHS) l).getIdentifier());
        Collections.reverse(lhsList);
        return lhsList.toArray(new String[0]);
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
    public static LeftHandSide getLHSforExpression(Expression e) {
        assert e instanceof IdentifierExpression
                || e instanceof StructAccessExpression
                || e instanceof ArrayAccessExpression;
        ILocation loc = e.getLocation();
        if (e instanceof IdentifierExpression) {
            IdentifierExpression ie = (IdentifierExpression) e;
            return new VariableLHS(loc, ie.getType(), ie.getIdentifier());
        }
        if (e instanceof StructAccessExpression) {
            StructAccessExpression sae = (StructAccessExpression) e;
            LeftHandSide lhs = getLHSforExpression(sae.getStruct());
            return new StructLHS(loc, sae.getType(), lhs, sae.getField());
        }
        if (e instanceof ArrayAccessExpression) {
            ArrayAccessExpression aae = (ArrayAccessExpression) e;
            LeftHandSide lhs = getLHSforExpression(aae.getArray());
            return new ArrayLHS(loc, aae.getType(), lhs, aae.getIndices());
        }
        throw new IllegalArgumentException(
                "Wrong implementation! This method is not intended to handle this argument!");
    }
}
