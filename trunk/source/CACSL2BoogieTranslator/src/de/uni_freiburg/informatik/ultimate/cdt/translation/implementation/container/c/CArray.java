/**
 * Describes an array given in C.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.CACSLLocation;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.InferredType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.AssertStatement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.result.Check;

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

    private final boolean incomplete;
    
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
    public CArray(Expression[] dimensions,
            CType valueType) {
        super(false, false, false, false); //FIXME: integrate those flags
        this.dimensions = dimensions;
        this.valueType = valueType;
        this.incomplete = false;
    }
    
    public CArray(Expression[] dimensions,
            CType valueType, boolean incomplete) {
        super(false, false, false, false); //FIXME: integrate those flags
        assert incomplete : "use other constructor otherwise";
        this.valueType = valueType;
        this.dimensions = dimensions;
        this.incomplete = true;
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
            throw new IncorrectSyntaxException(loc, msg);
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
        Check check = new Check(Check.Spec.ARRAY_INDEX);
        AssertStatement assertStmt = new AssertStatement(
                new CACSLLocation(loc, check), conjunction);
        check.addToNodeAnnot(assertStmt);
        return assertStmt;
    }

    @Override
    public String toString() {
        StringBuilder id = new StringBuilder("ARRAY#");
        StringBuilder dimString = new StringBuilder("_");
        for (Expression dim : getDimensions()) {
            if (dim instanceof BinaryExpression ||
                    dim instanceof UnaryExpression) {
                dim = getArithmeticResultAsIntegerLiteral(dim);
            }
            if (dim instanceof IntegerLiteral) {
                dimString.append(((IntegerLiteral) dim).getValue());
                dimString.append("_");
            }
            else {
                dimString = new StringBuilder("incomplete");
                break;
            }
        }
        
        if (incomplete) {
        	id.append("_INCOMPLETE");
        }
//        id.append(getDimensions().length);
        id.append(dimString.toString());
        id.append("~");
        id.append(valueType.toString());
        id.append("#");
        return id.toString();
    }
    
    public boolean isIncomplete() {
    	return this.incomplete;
    }
    
    /**
     * Computes the result of an integer arithmetic expression and
     * returns an the IntegerLiteral.
     * 
     * @param loc location
     * @param e arithmetic expression in the integers
     * @return expression of the resulting integer
     */
    private IntegerLiteral getArithmeticResultAsIntegerLiteral(Expression e) {
        assert (e instanceof UnaryExpression || e instanceof BinaryExpression);
        return new IntegerLiteral(e.getLocation(),
                Integer.toString(getArithmeticResultAsInteger(e)));
    }
    
    /**
     * Helper method for the computation of an arithmetic result from
     * expressions.
     * 
     * @param e expression (unary or binary)
     * @return the result as an int
     */
    private int getArithmeticResultAsInteger(Expression e) {
        if (e instanceof IntegerLiteral) {
            return Integer.parseInt(((IntegerLiteral)e).getValue());
        }
        assert (e instanceof UnaryExpression || e instanceof BinaryExpression);
        if (e instanceof BinaryExpression) {
            BinaryExpression be = (BinaryExpression)e;
            BinaryExpression.Operator operator = be.getOperator();
            int left = getArithmeticResultAsInteger(be.getLeft());
            int right = getArithmeticResultAsInteger(be.getRight());
            if (operator.equals(Operator.ARITHPLUS)) {
                return left + right;
            }
            else if (operator.equals(Operator.ARITHMINUS)) {
                return left - right;
            }
            else if (operator.equals(Operator.ARITHMUL)) {
                return left * right;
            }
            else if (operator.equals(Operator.ARITHDIV)) {
                return left / right;
            }
            else if (operator.equals(Operator.ARITHMOD)) {
                return left % right;
            }
            else {
                throw new UnsupportedSyntaxException(e.getLocation(),
                        "arithmetic expression with oeprator " + operator);
            }
        } else {
            UnaryExpression ue = (UnaryExpression)e;
            UnaryExpression.Operator operator = ue.getOperator();
            if (! operator.equals(UnaryExpression.Operator.ARITHNEGATIVE)) {
                throw new UnsupportedSyntaxException(e.getLocation(),
                        "arithmetic expression with oeprator " + operator);
            }
            return 0 - getArithmeticResultAsInteger(ue.getExpr());
        }
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof CType)) {
            return false;
        }
        CType oType = ((CType)o).getUnderlyingType();
        if (!(oType instanceof CArray)) {
            return false;
        }
        
        CArray oArr = (CArray)oType;
        if (!(valueType.equals(oArr.valueType))) {
            return false;
        }
        if (dimensions.length != oArr.dimensions.length) {
            return false;
        }
        for (int i = dimensions.length - 1; i >= 0; --i) {
            if (!(dimensions[i].equals(oArr.dimensions[i]))) {
                return false;
            }
        }
        return true;
    }
}
