/**
 * Describes an array given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import org.eclipse.cdt.core.dom.ast.IASTDeclSpecifier;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.result.Check;
import de.uni_freiburg.informatik.ultimate.result.SyntaxErrorResult.SyntaxErrorType;

/**
 * @author Markus Lindenmann
 * @date 18.09.2012
 */
public class CArray extends CType {
    /**
     * Array dimensions.
     */
    private final Expression[] dimensions;
    /**
     * Array type.
     */
    private final CType valueType;

    /**
     * Constructor.
     * 
     * @param dimensions
     *            the dimensions of this array.
     * @param valueType
     *            the type of the array.
     * @param cDeclSpec
     *            the C declaration used.
     */
    public CArray(IASTDeclSpecifier cDeclSpec, Expression[] dimensions,
            CType valueType) {
        super(cDeclSpec);
        this.dimensions = dimensions;
        this.valueType = valueType;
    }

    /**
     * @return the dimensions
     */
    public Expression[] getDimensions() {
        return dimensions.clone();
    }

    /**
     * @return the valueType
     */
    public CType getValueType() {
        return valueType;
    }

    /**
     * Generates and returns assert statements for an array access, checking the
     * indices to be smaller then the size of the declared array.
     * 
     * @param loc
     *            the location of the access, annotated with Check.
     * @param accessedIndices
     *            the indices that are being accessed
     * @return an assert statement.
     */
    public AssertStatement getAccessAsserts(CACSLLocation loc,
            Expression[] accessedIndices) {
        if (dimensions.length <= 0
                || accessedIndices.length != dimensions.length) {
            String msg = "Invalid array access! Too many or too few dimensions!";
            Dispatcher.error(loc, SyntaxErrorType.IncorrectSyntax, msg);
            throw new IncorrectSyntaxException(msg);
        }
        Expression int0 = new IntegerLiteral(loc, new InferredType(
                InferredType.Type.Integer), SFO.NR0);
        Expression conjunction = null;
        for (int i = 0; i < dimensions.length; i++) {
            Expression inner;
            // idx < dimSize
            inner = new BinaryExpression(loc, BinaryExpression.Operator.COMPLT,
                    accessedIndices[i], dimensions[i]);
            // dimSize > 0
            inner = new BinaryExpression(loc, Operator.LOGICAND, inner,
                    new BinaryExpression(loc, BinaryExpression.Operator.COMPGT,
                            dimensions[i], int0));
            // idx >= 0
            inner = new BinaryExpression(loc, Operator.LOGICAND, inner,
                    new BinaryExpression(loc,
                            BinaryExpression.Operator.COMPGEQ,
                            accessedIndices[i], int0));
            if (conjunction == null) {
                conjunction = inner;
            } else {
                conjunction = new BinaryExpression(loc, Operator.LOGICAND,
                        conjunction, inner);
            }
        }
        if (conjunction == null) {
            conjunction = new BooleanLiteral(loc, true);
        }
        return new AssertStatement(new CACSLLocation(loc, new Check(
                Check.Spec.ARRAY_INDEX)), conjunction);
    }

    @Override
    public String toString() {
        StringBuilder id = new StringBuilder("ARRAY#");
        id.append(getDimensions().length);
        id.append("~");
        id.append(valueType.toString());
        id.append("#");
        return id.toString();
    }
}
