package de.uni_freiburg.informatik.ultimate.boogie.ast;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class IfThenExpression extends Expression{

	private static final long serialVersionUID = 1L;
    private static final java.util.function.Predicate<BoogieASTNode> VALIDATOR = 
			BoogieASTNode.VALIDATORS.get(IfThenExpression.class);
    /**
     * The condition of this if then expression.
     */
    Expression condition;

    /**
     * The then part of this if then expression.
     */
    Expression thenPart;

    /**
     * The constructor taking initial values.
     * @param loc the location of this node
     * @param condition the condition of this if then else expression.
     * @param thenPart the then part of this if then else expression.
     */
    public IfThenExpression(ILocation loc, Expression condition, Expression thenPart) {
        super(loc);
        this.condition = condition;
        this.thenPart = thenPart;
        assert VALIDATOR == null || VALIDATOR.test(this) : "Invalid IfThenExpression: " + this;
    }

    /**
     * The constructor taking initial values.
     * @param loc the location of this node
     * @param type the type of this expression.
     * @param condition the condition of this if then else expression.
     * @param thenPart the then part of this if then else expression.
     */
    public IfThenExpression(ILocation loc, IBoogieType type, Expression condition, Expression thenPart) {
        super(loc, type);
        this.condition = condition;
        this.thenPart = thenPart;
        assert VALIDATOR == null || VALIDATOR.test(this) : "Invalid IfThenExpression: " + this;
    }

    /**
     * Returns a textual description of this object.
     */
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append("IfThenElseExpression").append('[');
        sb.append(condition);
        sb.append(',').append(thenPart);
        return sb.append(']').toString();
    }

    /**
     * Gets the condition of this if then else expression.
     * @return the condition of this if then else expression.
     */
    public Expression getCondition() {
        return condition;
    }

    /**
     * Gets the then part of this if then else expression.
     * @return the then part of this if then else expression.
     */
    public Expression getThenPart() {
        return thenPart;
    }

    public List<BoogieASTNode> getOutgoingNodes() {
        List<BoogieASTNode> children = super.getOutgoingNodes();
        children.add(condition);
        children.add(thenPart);
        return children;
    }

    public void accept(GeneratedBoogieAstVisitor visitor) {
        if (visitor.visit((Expression)this)) {
            //visit parent types higher up if necessary
        } else {
            return;
        }
        if (visitor.visit(this)) {
            if(condition!=null){
                condition.accept(visitor);
            }
            if(thenPart!=null){
                thenPart.accept(visitor);
            }
        }
    }

    public Expression accept(GeneratedBoogieAstTransformer visitor) {
        Expression node = visitor.transform(this);
        if(node != this){
            return node;
        }

            Expression newcondition = null;
        if(condition != null){
            newcondition = (Expression)condition.accept(visitor);
        }
            Expression newthenPart = null;
        if(thenPart != null){
            newthenPart = (Expression)thenPart.accept(visitor);
        }
        if(condition != newcondition || thenPart != newthenPart){
            return new IfThenExpression(loc, type, newcondition, newthenPart);
        }
        return this;
    }

}
