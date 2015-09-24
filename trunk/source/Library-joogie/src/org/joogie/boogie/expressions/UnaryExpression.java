/**
 * 
 */
package org.joogie.boogie.expressions;

import java.util.List;

import org.joogie.boogie.types.BoogieType;

/**
 * A class for expressions with unary operators
 * 
 * @author sergio
 * 
 */
public class UnaryExpression extends Expression {

	/**
	 * @param op
	 *            The prefix operator
	 * @param exp
	 *            The expression
	 */
	public UnaryExpression(UnaryOperator op, Expression exp) {
		super();
		this.exp = exp;
		this.op = op;
	}

	/**
	 * Default constructor
	 */
	public UnaryExpression() {
		this(null, null);
	}

	private Expression exp;

	/**
	 * @return the expression
	 */
	protected Expression getExpression() {
		return exp;
	}

	/**
	 * @param exp
	 *            the expression to set
	 */
	protected void setExpression(Expression exp) {
		this.exp = exp;
	}

	/**
	 * @return the operator
	 */
	protected UnaryOperator getOperator() {
		return op;
	}

	/**
	 * @param op
	 *            the operator to set
	 */
	protected void setOperator(UnaryOperator op) {
		this.op = op;
	}

	private UnaryOperator op;

	public enum UnaryOperator {
		Not("!"), Minus("-");
		private String description;

		UnaryOperator(String des) {
			description = des;
		}

		@Override
		public String toString() {
			return description;
		}
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#toBoogie()
	 */
	@Override
	public String toBoogie() {
		StringBuilder sb = new StringBuilder();
		sb.append(op.toString());
		sb.append(exp.toBoogie());
		return sb.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#getType()
	 */
	@Override
	public BoogieType getType() {
		return exp.getType();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#clone()
	 */
	@Override
	public Expression clone() {
		return new UnaryExpression(this.op, this.exp.clone());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.joogie.boogie.expressions.Expression#getUsedVariables()
	 */
	@Override
	public List<Variable> getUsedVariables() {
		return exp.getUsedVariables();
	}

}
