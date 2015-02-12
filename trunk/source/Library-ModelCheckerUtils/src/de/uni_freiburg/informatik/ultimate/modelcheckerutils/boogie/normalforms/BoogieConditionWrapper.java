package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.output.BoogiePrettyPrinter;

public class BoogieConditionWrapper implements IConditionWrapper<Expression> {

	public BoogieConditionWrapper() {

	}

	@Override
	public Collection<? extends Expression> normalizeNesting(Expression formula, Expression subformula) {
		if (formula instanceof BinaryExpression && subformula instanceof BinaryExpression) {
			BinaryExpression binExp = (BinaryExpression) formula;
			BinaryExpression subBinExp = (BinaryExpression) subformula;
			if (binExp.getOperator().equals(subBinExp.getOperator())) {
				return getOperands((BinaryExpression) subformula);
			}
		}
		return Collections.singleton(subformula);
	}

	@Override
	public Expression makeFalse() {
		return new BooleanLiteral(null, false);
	}

	@Override
	public Expression makeTrue() {
		return new BooleanLiteral(null, true);
	}

	@Override
	public Expression makeAnd(Expression left, Expression right) {
		if (left.equals(right)) {
			return left;
		}
		ArrayList<Expression> operands = new ArrayList<>(2);
		operands.add(left);
		operands.add(right);
		return makeBinop(Operator.LOGICAND, operands.iterator());
	}

	@Override
	public Expression makeOr(Iterator<Expression> operands) {
		return makeBinop(Operator.LOGICOR, operands);
	}

	@Override
	public Expression makeAnd(Iterator<Expression> operands) {
		return makeBinop(Operator.LOGICAND, operands);
	}

	private Expression makeBinop(Operator op, Iterator<Expression> operands) {
		Expression left = null;
		Expression right = null;
		Iterator<Expression> unifiedOperandsIterator = unifyOperands(op, operands);
		while (unifiedOperandsIterator.hasNext()) {
			left = right;
			right = unifiedOperandsIterator.next();
			if (left == null) {
				continue;
			}
			right = new BinaryExpression(left.getLocation(), op, left, right);
			if (!unifiedOperandsIterator.hasNext()) {
				// System.out.println("New Binop: " +
				// BoogiePrettyPrinter.print(right));
				return right;
			}
		}
		if (left == null && right != null) {
			// unification left us with only one operand
			return right;
		}
		if (left == null && right == null) {
			throw new IllegalArgumentException("You must supply operands to this method");
		}
		// System.out.println("New Binop: " + BoogiePrettyPrinter.print(left));
		return left;
	}

	private Iterator<Expression> unifyOperands(Operator op, Iterator<Expression> operands) {
		LinkedHashSet<Expression> unifiedOperands = new LinkedHashSet<>();
		while (operands.hasNext()) {
			Expression operand = operands.next();
			if (operand instanceof BinaryExpression) {
				BinaryExpression binOperand = (BinaryExpression) operand;
				if (binOperand.getOperator().equals(op)) {
					unifiedOperands.addAll(getOperands(binOperand));
				} else {
					unifiedOperands.add(operand);
				}
			} else {
				unifiedOperands.add(operand);
			}
			operands.remove();
		}

		// System.out.println("Unified for " + op + ": " +
		// printExpressionCollection(unifiedOperands));
		return unifiedOperands.iterator();
	}

	// private String printExpressionCollection(Collection<Expression> exp) {
	// StringBuilder sb = new StringBuilder();
	// sb.append("[");
	// for (Expression e : exp) {
	// sb.append(BoogiePrettyPrinter.print(e)).append(", ");
	// }
	// sb.delete(sb.length() - 2, sb.length());
	// sb.append("]");
	// return sb.toString();
	// }

	@Override
	public Expression makeNot(Expression operand) {
		return new UnaryExpression(operand.getLocation(), UnaryExpression.Operator.LOGICNEG, operand);
	}

	@Override
	public Expression getOperand(Expression formula) {
		if (formula instanceof UnaryExpression) {
			UnaryExpression exp = (UnaryExpression) formula;
			return exp.getExpr();
		} else if (formula instanceof QuantifierExpression) {
			QuantifierExpression exp = (QuantifierExpression) formula;
			return exp.getSubformula();
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterator<Expression> getOperands(Expression formula) {
		if (formula instanceof UnaryExpression) {
			UnaryExpression exp = (UnaryExpression) formula;
			ArrayList<Expression> rtr = new ArrayList<>(1);
			rtr.add(exp.getExpr());
			return rtr.iterator();
		} else if (formula instanceof BinaryExpression) {
			return getOperands((BinaryExpression) formula).iterator();
		} else if (formula instanceof QuantifierExpression) {
			QuantifierExpression exp = (QuantifierExpression) formula;
			ArrayList<Expression> rtr = new ArrayList<>(1);
			rtr.add(exp.getSubformula());
			return rtr.iterator();
		}
		throw new UnsupportedOperationException();
	}

	private Collection<Expression> getOperands(BinaryExpression expr) {
		ArrayDeque<Expression> open = new ArrayDeque<>();
		LinkedHashSet<Expression> closed = new LinkedHashSet<>();
		open.add(expr.getLeft());
		open.add(expr.getRight());
		Operator currentOp = expr.getOperator();

		while (!open.isEmpty()) {
			Expression current = open.removeLast();
			if (current instanceof BinaryExpression) {
				BinaryExpression candidate = (BinaryExpression) current;
				if (candidate.getOperator() == currentOp) {
					open.add(candidate.getLeft());
					open.add(candidate.getRight());
					continue;
				}
			}
			closed.add(current);
		}
		return closed;
	}

	@Override
	public boolean isAtom(Expression formula) {
		return !isNot(formula) && !isAnd(formula) && !isOr(formula) && !isForall(formula) && !isExists(formula);
	}

	@Override
	public boolean isNot(Expression formula) {
		if (formula instanceof UnaryExpression) {
			UnaryExpression unexpr = (UnaryExpression) formula;
			return unexpr.getOperator() == UnaryExpression.Operator.LOGICNEG;
		}
		return false;
	}

	@Override
	public boolean isAnd(Expression formula) {
		if (formula instanceof BinaryExpression) {
			BinaryExpression binexpr = (BinaryExpression) formula;
			return binexpr.getOperator() == Operator.LOGICAND;
		}
		return false;
	}

	@Override
	public boolean isOr(Expression formula) {
		if (formula instanceof BinaryExpression) {
			BinaryExpression binexpr = (BinaryExpression) formula;
			return binexpr.getOperator() == Operator.LOGICOR;
		}
		return false;
	}

	@Override
	public boolean isExists(Expression formula) {
		return formula instanceof QuantifierExpression && !((QuantifierExpression) formula).isUniversal();
	}

	@Override
	public boolean isForall(Expression formula) {
		return formula instanceof QuantifierExpression && ((QuantifierExpression) formula).isUniversal();
	}

	@Override
	public Expression changeForall(Expression oldForAll, Expression operand) {
		QuantifierExpression old = (QuantifierExpression) oldForAll;
		return new QuantifierExpression(operand.getLocation(), true, old.getTypeParams(), old.getParameters(),
				old.getAttributes(), operand);
	}

	@Override
	public Expression changeExists(Expression oldExists, Expression operand) {
		QuantifierExpression old = (QuantifierExpression) oldExists;
		return new QuantifierExpression(operand.getLocation(), false, old.getTypeParams(), old.getParameters(),
				old.getAttributes(), operand);
	}

	@Override
	public boolean isEqual(Expression one, Expression other) {
		if (one == null || other == null) {
			return false;
		}

		if (one.getClass().equals(other.getClass())) {
			if (one instanceof BooleanLiteral) {
				return ((BooleanLiteral) one).getValue() == ((BooleanLiteral) other).getValue();
			}
		}

		return one.equals(other);
	}

	@Override
	public Expression rewritePredNotEquals(Expression atom) {
		if (atom instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) atom;
			if (binexp.getOperator() == Operator.COMPNEQ) {
				Expression left = new BinaryExpression(atom.getLocation(), Operator.COMPLT, binexp.getLeft(),
						binexp.getRight());
				Expression right = new BinaryExpression(atom.getLocation(), Operator.COMPGT, binexp.getLeft(),
						binexp.getRight());
				return new BinaryExpression(atom.getLocation(), Operator.LOGICOR, left, right);
			}
		}
		return atom;
	}

	@Override
	public Expression negatePred(Expression atom) {
		if (atom instanceof BinaryExpression) {
			BinaryExpression binexp = (BinaryExpression) atom;
			Operator negatedOp;
			switch (binexp.getOperator()) {
			case ARITHDIV:
			case ARITHMINUS:
			case ARITHMOD:
			case ARITHMUL:
			case ARITHPLUS:
			case BITVECCONCAT:
				throw new UnsupportedOperationException("Cannot negate non-boolean terms");
			case LOGICAND:
			case LOGICIFF:
			case LOGICIMPLIES:
			case LOGICOR:
				throw new UnsupportedOperationException(BoogiePrettyPrinter.print(atom) + " is no predicate");
			case COMPPO:
				throw new UnsupportedOperationException("Dont know how to negate partial order");
			case COMPEQ:
				negatedOp = Operator.COMPNEQ;
				break;
			case COMPGEQ:
				negatedOp = Operator.COMPLT;
				break;
			case COMPGT:
				negatedOp = Operator.COMPLEQ;
				break;
			case COMPLEQ:
				negatedOp = Operator.COMPGT;
				break;
			case COMPLT:
				negatedOp = Operator.COMPGEQ;
				break;
			case COMPNEQ:
				negatedOp = Operator.COMPEQ;
				break;
			default:
				throw new UnsupportedOperationException("Unknown operator");
			}
			return new BinaryExpression(atom.getLocation(), negatedOp, binexp.getLeft(), binexp.getRight());
		} else if (atom instanceof BooleanLiteral) {
			BooleanLiteral lit = (BooleanLiteral) atom;
			return new BooleanLiteral(lit.getLocation(), !lit.getValue());
		}
		if (atom != null) {
			throw new UnsupportedOperationException(BoogiePrettyPrinter.print(atom) + " is no predicate");
		} else {
			throw new NullPointerException();
		}
	}
}
