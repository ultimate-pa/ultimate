/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.boogie;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashSet;

import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BooleanLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.QuantifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.boogie.output.BoogiePrettyPrinter;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieConstructedType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogiePrimitiveType;
import de.uni_freiburg.informatik.ultimate.boogie.type.BoogieType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IBoogieType;
import de.uni_freiburg.informatik.ultimate.util.simplifier.INormalFormable;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class BoogieExpressionTransformer implements INormalFormable<Expression> {

	@Override
	public Collection<? extends Expression> normalizeNesting(final Expression formula, final Expression subformula) {
		if (formula instanceof BinaryExpression && subformula instanceof BinaryExpression) {
			final BinaryExpression binExp = (BinaryExpression) formula;
			final BinaryExpression subBinExp = (BinaryExpression) subformula;
			if (binExp.getOperator().equals(subBinExp.getOperator())) {
				return getOperands((BinaryExpression) subformula);
			}
		}
		return Collections.singleton(subformula);
	}

	@Override
	public Expression makeFalse() {
		return new BooleanLiteral(null, BoogieType.TYPE_BOOL, false);
	}

	@Override
	public Expression makeTrue() {
		return new BooleanLiteral(null, BoogieType.TYPE_BOOL, true);
	}

	@Override
	public Expression makeAnd(final Expression left, final Expression right) {
		if (left.equals(right)) {
			return left;
		}
		final ArrayList<Expression> operands = new ArrayList<>(2);
		operands.add(left);
		operands.add(right);
		return makeBoolBinop(Operator.LOGICAND, operands.iterator());
	}

	@Override
	public Expression makeOr(final Iterator<Expression> operands) {
		return makeBoolBinop(Operator.LOGICOR, operands);
	}

	@Override
	public Expression makeAnd(final Iterator<Expression> operands) {
		return makeBoolBinop(Operator.LOGICAND, operands);
	}

	private static Expression makeBoolBinop(final Operator op, final Iterator<Expression> operands) {
		Expression left = null;
		Expression right = null;
		final Iterator<Expression> unifiedOperandsIterator = unifyOperands(op, operands);
		while (unifiedOperandsIterator.hasNext()) {
			left = right;
			right = unifiedOperandsIterator.next();
			if (left == null) {
				continue;
			}
			right = new BinaryExpression(left.getLocation(), BoogieType.TYPE_BOOL, op, left, right);
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

	private static Iterator<Expression> unifyOperands(final Operator op, final Iterator<Expression> operands) {
		final LinkedHashSet<Expression> unifiedOperands = new LinkedHashSet<>();
		while (operands.hasNext()) {
			final Expression operand = operands.next();
			if (operand instanceof BinaryExpression) {
				final BinaryExpression binOperand = (BinaryExpression) operand;
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
		return unifiedOperands.iterator();
	}

	@Override
	public Expression makeNot(final Expression operand) {
		return new UnaryExpression(operand.getLocation(), BoogieType.TYPE_BOOL, UnaryExpression.Operator.LOGICNEG,
				operand);
	}

	@Override
	public Expression getOperand(final Expression formula) {
		if (formula instanceof UnaryExpression) {
			final UnaryExpression exp = (UnaryExpression) formula;
			return exp.getExpr();
		} else if (formula instanceof QuantifierExpression) {
			final QuantifierExpression exp = (QuantifierExpression) formula;
			return exp.getSubformula();
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public Iterator<Expression> getOperands(final Expression formula) {
		if (formula instanceof UnaryExpression) {
			final UnaryExpression exp = (UnaryExpression) formula;
			final ArrayList<Expression> rtr = new ArrayList<>(1);
			rtr.add(exp.getExpr());
			return rtr.iterator();
		} else if (formula instanceof BinaryExpression) {
			return getOperands((BinaryExpression) formula).iterator();
		} else if (formula instanceof QuantifierExpression) {
			final QuantifierExpression exp = (QuantifierExpression) formula;
			final ArrayList<Expression> rtr = new ArrayList<>(1);
			rtr.add(exp.getSubformula());
			return rtr.iterator();
		}
		throw new UnsupportedOperationException();
	}

	private static Collection<Expression> getOperands(final BinaryExpression expr) {
		final ArrayDeque<Expression> open = new ArrayDeque<>();
		final LinkedHashSet<Expression> closed = new LinkedHashSet<>();
		open.add(expr.getLeft());
		open.add(expr.getRight());
		final Operator currentOp = expr.getOperator();

		while (!open.isEmpty()) {
			final Expression current = open.removeLast();
			if (current instanceof BinaryExpression) {
				final BinaryExpression candidate = (BinaryExpression) current;
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
	public boolean isAtom(final Expression formula) {
		return !isNot(formula) && !isAnd(formula) && !isOr(formula) && !isForall(formula) && !isExists(formula);
	}

	@Override
	public boolean isNot(final Expression formula) {
		if (formula instanceof UnaryExpression) {
			final UnaryExpression unexpr = (UnaryExpression) formula;
			return unexpr.getOperator() == UnaryExpression.Operator.LOGICNEG;
		}
		return false;
	}

	@Override
	public boolean isAnd(final Expression formula) {
		if (formula instanceof BinaryExpression) {
			final BinaryExpression binexpr = (BinaryExpression) formula;
			return binexpr.getOperator() == Operator.LOGICAND;
		}
		return false;
	}

	@Override
	public boolean isOr(final Expression formula) {
		if (formula instanceof BinaryExpression) {
			final BinaryExpression binexpr = (BinaryExpression) formula;
			return binexpr.getOperator() == Operator.LOGICOR;
		}
		return false;
	}

	@Override
	public boolean isExists(final Expression formula) {
		return formula instanceof QuantifierExpression && !((QuantifierExpression) formula).isUniversal();
	}

	@Override
	public boolean isForall(final Expression formula) {
		return formula instanceof QuantifierExpression && ((QuantifierExpression) formula).isUniversal();
	}

	@Override
	public Expression changeForall(final Expression oldForAll, final Expression operand) {
		final QuantifierExpression old = (QuantifierExpression) oldForAll;
		return new QuantifierExpression(operand.getLocation(), true, old.getTypeParams(), old.getParameters(),
				old.getAttributes(), operand);
	}

	@Override
	public Expression changeExists(final Expression oldExists, final Expression operand) {
		final QuantifierExpression old = (QuantifierExpression) oldExists;
		return new QuantifierExpression(operand.getLocation(), false, old.getTypeParams(), old.getParameters(),
				old.getAttributes(), operand);
	}

	@Override
	public boolean isEqual(final Expression one, final Expression other) {
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
	public Expression rewritePredNotEquals(final Expression atom) {
		if (atom instanceof BinaryExpression) {
			final BinaryExpression binexp = (BinaryExpression) atom;
			if (binexp.getOperator() != Operator.COMPNEQ) {
				return atom;
			}
			final IBoogieType lType = binexp.getLeft().getType();
			if (!isAnyPrimitiveType(lType) || isPrimitiveType(lType, BoogieType.TYPE_BOOL)) {
				return atom;
			}

			final Expression left = new BinaryExpression(atom.getLocation(), BoogieType.TYPE_BOOL, Operator.COMPLT,
					binexp.getLeft(), binexp.getRight());
			final Expression right = new BinaryExpression(atom.getLocation(), BoogieType.TYPE_BOOL, Operator.COMPGT,
					binexp.getLeft(), binexp.getRight());
			return new BinaryExpression(atom.getLocation(), BoogieType.TYPE_BOOL, Operator.LOGICOR, left, right);
		}
		return atom;
	}

	@Override
	public Expression negatePred(final Expression atom) {
		if (atom instanceof BinaryExpression) {
			final BinaryExpression binexp = (BinaryExpression) atom;
			final Operator negatedOp;
			switch (binexp.getOperator()) {
			case ARITHDIV:
			case ARITHMINUS:
			case ARITHMOD:
			case ARITHMUL:
			case ARITHPLUS:
			case BITVECCONCAT:
				// this is a type error and should not happen
				throw new UnsupportedOperationException("Cannot negate non-boolean terms");
			case LOGICAND:
			case LOGICIFF:
			case LOGICIMPLIES:
			case LOGICOR:
				// this is a contract violation and should not happen
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
			return new BinaryExpression(atom.getLocation(), BoogieType.TYPE_BOOL, negatedOp, binexp.getLeft(),
					binexp.getRight());
		} else if (atom instanceof BooleanLiteral) {
			final BooleanLiteral lit = (BooleanLiteral) atom;
			return new BooleanLiteral(lit.getLocation(), BoogieType.TYPE_BOOL, !lit.getValue());
		} else if (atom instanceof UnaryExpression) {
			final UnaryExpression uexp = (UnaryExpression) atom;
			switch (uexp.getOperator()) {
			case ARITHNEGATIVE:
				throw new UnsupportedOperationException("Cannot negate non-boolean terms");
			case LOGICNEG:
				return uexp.getExpr();
			case OLD:
				throw new UnsupportedOperationException(BoogiePrettyPrinter.print(atom) + " is no predicate");
			default:
				throw new UnsupportedOperationException("Unknown operator");
			}
		}
		// cannot negate anything else
		throw new UnsupportedOperationException("Cannot negate " + BoogiePrettyPrinter.print(atom));
	}

	@Override
	public boolean isLiteral(final Expression formula) {
		if (formula instanceof IdentifierExpression || formula instanceof BooleanLiteral) {
			return true;
		}
		if (formula instanceof UnaryExpression) {
			final Expression innerExpr = ((UnaryExpression) formula).getExpr();
			return innerExpr instanceof IdentifierExpression || innerExpr instanceof BooleanLiteral;
		}
		return false;
	}

	private static boolean isPrimitiveType(final IBoogieType type, final BoogiePrimitiveType desiredType) {
		if (type instanceof BoogiePrimitiveType) {
			return ((BoogiePrimitiveType) type).getTypeCode() == desiredType.getTypeCode();
		} else if (type instanceof BoogieConstructedType) {
			final BoogieConstructedType ctype = (BoogieConstructedType) type;
			if (ctype.getUnderlyingType() instanceof BoogieConstructedType) {
				return false;
			}
			if (ctype.getUnderlyingType() == ctype) {
				return false;
			}
			return isPrimitiveType(ctype.getUnderlyingType(), desiredType);
		}
		return false;
	}

	private static boolean isAnyPrimitiveType(final IBoogieType type) {
		if (type == null) {
			throw new IllegalArgumentException("type is null");
		}
		if (type instanceof BoogiePrimitiveType) {
			return true;
		} else if (type instanceof BoogieConstructedType) {
			final BoogieConstructedType ctype = (BoogieConstructedType) type;
			if (ctype.getUnderlyingType() instanceof BoogieConstructedType) {
				return false;
			}
			if (ctype.getUnderlyingType() == ctype) {
				return false;
			}
			return isAnyPrimitiveType(ctype.getUnderlyingType());
		}
		return false;
	}

	@Override
	public boolean isTrue(final Expression formula) {
		return formula instanceof BooleanLiteral && ((BooleanLiteral) formula).getValue();
	}

	@Override
	public boolean isFalse(final Expression formula) {
		return formula instanceof BooleanLiteral && !((BooleanLiteral) formula).getValue();
	}
}
