/**
 * 
 */
package soottocfg.cfg.expression;

import java.util.HashSet;
import java.util.Set;

import soottocfg.cfg.Variable;
import soottocfg.cfg.type.BoolType;
import soottocfg.cfg.type.Type;

/**
 * @author schaef
 *
 */
public class BinaryExpression extends Expression {

	public enum BinaryOperator {
		Plus("+"), Minus("-"), Mul("*"), Div("/"), Mod("%"), And("&&"), Or("||"), Xor("^"), Implies("->"), Eq("=="), Ne(
				"!="), Gt(">"), Ge(">="), Lt("<"), Le("<="), Shl("<<"), Shr(">>"), Ushr("u>>"), BOr("|"), BAnd("&");

		private final String name;

		private BinaryOperator(String s) {
			name = s;
		}

		public boolean equalsName(String otherName) {
			return (otherName == null) ? false : name.equals(otherName);
		}

		@Override
		public String toString() {
			return this.name;
		}
	}

	private final Expression left, right;
	private final BinaryOperator op;

	public BinaryExpression(BinaryOperator op, Expression left, Expression right) {
		this.left = left;
		this.right = right;
		this.op = op;
	}

	public Expression getLeft() {
		return left;
	}

	public Expression getRight() {
		return right;
	}

	public BinaryOperator getOp() {
		return op;
	}

	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(this.left);
		sb.append(" " + this.op + " ");
		sb.append(this.right);
		sb.append(")");
		return sb.toString();
	}

	@Override
	public Set<Variable> getUsedVariables() {
		Set<Variable> used = new HashSet<Variable>();
		used.addAll(left.getUsedVariables());
		used.addAll(right.getUsedVariables());
		return used;
	}

	@Override
	public Set<Variable> getLVariables() {
		//because this can't happen on the left.
		Set<Variable> used = new HashSet<Variable>();
		return used;
	}
	
	@Override
	public Type getType() {
		switch (op) {
		case Plus:
		case Minus:
		case Div:
		case Mod: {
			assert(left.getType().equals(right.getType()));
			return left.getType();			
		}
		case Eq:
		case Ne:
		case Gt:
		case Ge:
		case Lt:
		case Le: {
			assert(left.getType().equals(right.getType()));
			return BoolType.instance();			
		}
		case And:
		case Or:
		case Implies: {
			assert(left.getType()==BoolType.instance() && right.getType() == BoolType.instance() );
			return BoolType.instance();
		}
		default: {
			throw new RuntimeException("Not implemented for " + op);
		}
		}
	}

}
