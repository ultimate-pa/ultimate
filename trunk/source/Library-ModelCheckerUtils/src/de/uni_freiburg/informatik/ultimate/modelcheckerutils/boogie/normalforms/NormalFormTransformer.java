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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * NormalFormTransformer converts expressions or terms to various other forms (e.g., NNF, DNG, CNF, PNF, etc.). It has
 * to be used together with {@link INormalFormable}, which provides an interface for, e.g., Boogie or SMT s.t. the
 * operations here can ignore the specifics of the implementation.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class NormalFormTransformer<E> {

	private final INormalFormable<E> mWrapper;

	public NormalFormTransformer(final INormalFormable<E> wrapper) {
		mWrapper = wrapper;
	}

	/**
	 * Create negation normal form from parameter.
	 */
	public E toNnf(final E formula) {
		if (formula == null) {
			return null;
		}
		if (mWrapper.isAtom(formula)) {
			return formula;
		}

		if (mWrapper.isLiteral(formula)) {
			if (!mWrapper.isNot(formula)) {
				return formula;
			}
			final E inner = mWrapper.getOperand(formula);
			if (mWrapper.isTrue(inner)) {
				return mWrapper.makeFalse();
			}
			if (mWrapper.isFalse(inner)) {
				return mWrapper.makeTrue();
			}
			// neither true nor false but literal, so already in NNF
			return formula;
		}

		E current = formula;
		current = makeNnf(current);
		current = simplify(current);
		return current;
	}

	/**
	 * Create distributive normal form (DNF) from parameter.
	 */
	public E toDnf(final E formula) {
		if (formula == null) {
			return null;
		}
		if (mWrapper.isAtom(formula)) {
			return formula;
		}
		E current = formula;
		current = makeNnf(current);
		current = simplify(current);
		current = skolemize(current);
		current = makeDnf(current);
		current = simplifyDnf(current);
		return current;
	}

	/**
	 * <ol>
	 * <li>Create formula in NNF from parameter.
	 * <li>Pull negations further in, e.g. convert !(x != y) to (x == y)
	 * <li>Replace all terms of the form x != y with x < y || x > y
	 * </ol>
	 */
	public E rewriteNotEquals(final E formula) {
		if (formula == null) {
			return null;
		}
		final E nnfFormula = toNnf(formula);

		if (mWrapper.isAtom(nnfFormula)) {
			return mWrapper.rewritePredNotEquals(nnfFormula);
		} else if (mWrapper.isLiteral(nnfFormula)) {
			return nnfFormula;
		} else if (mWrapper.isNot(nnfFormula)) {
			// because the formula is in NNF, the negation can only be in front
			// of a term
			final E oper = mWrapper.getOperand(nnfFormula);
			final E neg = mWrapper.negatePred(oper);
			if (oper == neg) {
				// the operand cannot be negated any more
				return nnfFormula;
			}
			// the operand was negated
			return mWrapper.rewritePredNotEquals(neg);
		} else if (mWrapper.isAnd(nnfFormula)) {
			final Deque<E> operands = new ArrayDeque<>();
			final Iterator<E> iter = mWrapper.getOperands(nnfFormula);
			while (iter.hasNext()) {
				final E operand = rewriteNotEquals(iter.next());
				iter.remove();
				operands.addFirst(operand);
			}
			return mWrapper.makeAnd(operands.iterator());
		} else if (mWrapper.isOr(nnfFormula)) {
			final Deque<E> operands = new ArrayDeque<>();
			final Iterator<E> iter = mWrapper.getOperands(nnfFormula);
			while (iter.hasNext()) {
				final E operand = rewriteNotEquals(iter.next());
				iter.remove();
				operands.addFirst(operand);
			}
			return mWrapper.makeOr(operands.iterator());
		} else {
			throw new UnsupportedOperationException();
		}
	}

	/**
	 * Creates distributive normal form (DNF) from parameter, but provides a collection of disjuncts instead of a whole
	 * new formula.
	 */
	public Collection<E> toDnfDisjuncts(final E formula) {
		final E dnf = toDnf(formula);
		if (dnf == null) {
			return null;
		}
		if (!mWrapper.isOr(dnf)) {
			return Collections.singleton(dnf);
		}
		return toTermsTopLevel(dnf);
	}

	/**
	 * Simplifies formula by absorbing true, false, and, or.
	 */
	public E simplify(final E formula) {
		// TODO: Simplify negations by e.g. converting !(a == b) to (a != b)
		// TODO: Simplify overlapping and/or, e.g. a && (a || b) -> a
		if (mWrapper.isAnd(formula) || mWrapper.isOr(formula)) {
			return simplifyAndOr(formula);
		}
		return formula;
	}

	private Collection<E> toTermsTopLevel(final E formula) {
		if (formula == null) {
			return null;
		}

		final List<E> terms = new ArrayList<>();
		final Iterator<E> iter = mWrapper.getOperands(formula);
		while (iter.hasNext()) {
			terms.add(iter.next());
		}
		return terms;
	}

	private E simplifyDnf(final E formula) {
		final E simplFormula = simplify(formula);
		if (!mWrapper.isOr(simplFormula)) {
			// is singleton, cannot be simpler
			return simplFormula;
		}
		final Set<E> result = getSet(mWrapper.getOperands(simplFormula));

		final Iterator<E> operands = mWrapper.getOperands(simplFormula);
		while (operands.hasNext()) {
			final E current = operands.next();
			result.remove(current);

			boolean add = true;
			for (final E other : result) {
				if (isSubformula(current, other)) {
					add = false;
					break;
				}
			}

			if (add) {
				result.add(current);
			}
		}
		return mWrapper.makeOr(result.iterator());
	}

	private boolean isSubformula(final E root, final E candidate) {
		// requires normalized nesting
		if (mWrapper.isEqual(root, candidate)) {
			return true;
		}
		if (mWrapper.isAtom(root)) {
			return false;
		}

		if (mWrapper.isAtom(candidate)
				|| (mWrapper.isNot(candidate) && mWrapper.isAtom(mWrapper.getOperand(candidate)))) {
			if (isOperandSubset(root, candidate)) {
				return true;
			}
		} else if (mWrapper.isAnd(root) && mWrapper.isAnd(candidate)) {
			if (isOperandSubset(root, candidate)) {
				return true;
			}
		} else if (mWrapper.isOr(root) && mWrapper.isOr(candidate)) {
			if (isOperandSubset(root, candidate)) {
				return true;
			}
		}

		// descend
		final Iterator<E> operands = mWrapper.getOperands(root);
		while (operands.hasNext()) {
			if (isSubformula(operands.next(), candidate)) {
				return true;
			}
		}
		return false;
	}

	private boolean isOperandSubset(final E root, final E candidate) {
		final Set<E> operands = getSet(mWrapper.getOperands(root));
		final Iterator<E> childOperands = mWrapper.getOperands(candidate);
		boolean isSub = true;
		while (childOperands.hasNext()) {
			if (!operands.contains(childOperands.next())) {
				isSub = false;
			}
		}
		return isSub;
	}

	private LinkedHashSet<E> getSet(final Iterator<E> iter) {
		final LinkedHashSet<E> set = new LinkedHashSet<>();
		while (iter.hasNext()) {
			set.add(iter.next());
		}
		return set;
	}

	private E skolemize(final E current) {
		// TODO implement skolemization:
		// 1. unify variables
		// 2. move quantifiers outward
		// 3. insert skolem function to eliminate existential quantification
		// 4. drop all universal quantifiers
		return current;
	}

	private E makeDnf(final E current) {
		if (mWrapper.isAtom(current)) {
			// nothing to do, already finished
			return current;
		} else if (mWrapper.isNot(current)) {
			if (mWrapper.isAtom(mWrapper.getOperand(current))) {
				// nothing to do, is literal
				return current;
			}
			throw new AssertionError("Input not in NNF");
		} else if (mWrapper.isAnd(current)) {
			// apply distributivity
			final ArrayDeque<E> operands = new ArrayDeque<>();

			final Iterator<E> iter = mWrapper.getOperands(current);
			// first, make dnf for each operand
			while (iter.hasNext()) {
				final E operand = makeDnf(iter.next());
				iter.remove();
				operands.add(operand);
			}

			// then, distribute singletons with ors and eliminate redundant ones
			while (!operands.isEmpty()) {
				final E firstOperand = operands.removeLast();
				if (operands.isEmpty()) {
					// If there is no more or, we are finished.
					return firstOperand;
				}
				final E secondOperand = operands.removeLast();

				E or;
				E notOr;

				if (mWrapper.isOr(firstOperand)) {
					if (mWrapper.isOr(secondOperand)) {
						// Both operands are or, apply transformation (a || b) && (c || d)
						// to (a && c) || (a && d) || (b && c) || (b && d)

						final ArrayList<E> newOrOperands = new ArrayList<>();
						final Iterator<E> firstOrOperands = mWrapper.getOperands(firstOperand);
						while (firstOrOperands.hasNext()) {
							final Iterator<E> secondOrOperands = mWrapper.getOperands(secondOperand);
							final E currentOr = firstOrOperands.next();
							while (secondOrOperands.hasNext()) {
								newOrOperands.add(mWrapper.makeAnd(currentOr, secondOrOperands.next()));
								secondOrOperands.remove();
							}
							firstOrOperands.remove();
						}
						operands.addFirst(mWrapper.makeOr(newOrOperands.iterator()));
						continue;
					}
					or = firstOperand;
					notOr = secondOperand;
				} else if (mWrapper.isOr(secondOperand)) {
					or = secondOperand;
					notOr = firstOperand;
				} else {
					// both are not or, merge them
					operands.addFirst(mWrapper.makeAnd(firstOperand, secondOperand));
					continue;
				}

				// only one operand is or, apply
				// a && (b || c) = (a && b) || (a && c)
				final ArrayList<E> newOrOperands = new ArrayList<>();
				final Iterator<E> currentOrOperands = mWrapper.getOperands(or);
				while (currentOrOperands.hasNext()) {
					newOrOperands.add(mWrapper.makeAnd(currentOrOperands.next(), notOr));
					currentOrOperands.remove();
				}
				operands.addFirst(mWrapper.makeOr(newOrOperands.iterator()));
			}
			throw new AssertionError();
		} else if (mWrapper.isOr(current)) {
			// descend
			final ArrayList<E> inner = new ArrayList<>();
			final Iterator<E> iter = mWrapper.getOperands(current);
			while (iter.hasNext()) {
				inner.add(makeDnf(iter.next()));
			}
			return mWrapper.makeOr(inner.iterator());
		} else if (mWrapper.isExists(current)) {
			// descend
			return mWrapper.changeExists(current, makeDnf(mWrapper.getOperand(current)));
		} else if (mWrapper.isForall(current)) {
			return mWrapper.changeForall(current, makeDnf(mWrapper.getOperand(current)));
		} else {
			throw new AssertionError();
		}
	}

	private E makeNnf(final E condition) {
		if (mWrapper.isAtom(condition)) {
			// nothing to do here
			return condition;
		} else if (mWrapper.isNot(condition)) {
			final E operand = mWrapper.getOperand(condition);
			if (mWrapper.isTrue(operand)) {
				return mWrapper.makeFalse();
			} else if (mWrapper.isFalse(operand)) {
				return mWrapper.makeTrue();
			} else if (mWrapper.isAtom(operand)) {
				// is already in nnf
				return condition;
			} else if (mWrapper.isNot(operand)) {
				// remove double negation
				return makeNnf(mWrapper.getOperand(operand));
			} else if (mWrapper.isOr(operand)) {
				// use de morgan
				final ArrayDeque<E> inner = new ArrayDeque<>();
				final Iterator<E> iter = mWrapper.getOperands(operand);
				while (iter.hasNext()) {
					inner.add(makeNnf(mWrapper.makeNot(iter.next())));
				}
				return mWrapper.makeAnd(inner.iterator());
			} else if (mWrapper.isAnd(operand)) {
				// use de morgan
				final ArrayDeque<E> inner = new ArrayDeque<>();
				final Iterator<E> iter = mWrapper.getOperands(operand);
				while (iter.hasNext()) {
					inner.add(makeNnf(mWrapper.makeNot(iter.next())));
				}
				return mWrapper.makeOr(inner.iterator());
			} else if (mWrapper.isForall(operand)) {
				return mWrapper.changeExists(operand, makeNnf(mWrapper.makeNot(mWrapper.getOperand(operand))));
			} else if (mWrapper.isExists(operand)) {
				return mWrapper.changeForall(operand, makeNnf(mWrapper.makeNot(mWrapper.getOperand(operand))));
			} else {
				throw new AssertionError();
			}
		} else {
			// its no atom, its no not, descend
			if (mWrapper.isOr(condition)) {
				final ArrayDeque<E> inner = new ArrayDeque<>();
				final Iterator<E> iter = mWrapper.getOperands(condition);
				while (iter.hasNext()) {
					inner.add(makeNnf(iter.next()));
				}
				return mWrapper.makeOr(inner.iterator());
			} else if (mWrapper.isAnd(condition)) {
				final ArrayDeque<E> inner = new ArrayDeque<>();
				final Iterator<E> iter = mWrapper.getOperands(condition);
				while (iter.hasNext()) {
					inner.add(makeNnf(iter.next()));
				}
				return mWrapper.makeAnd(inner.iterator());
			} else if (mWrapper.isForall(condition)) {
				return mWrapper.changeForall(condition, makeNnf(mWrapper.getOperand(condition)));
			} else if (mWrapper.isExists(condition)) {
				return mWrapper.changeExists(condition, makeNnf(mWrapper.getOperand(condition)));
			} else {
				throw new AssertionError();
			}
		}
	}

	private E simplifyAndOr(final E formula) {
		final E trueTerm = mWrapper.makeTrue();
		final E falseTerm = mWrapper.makeFalse();
		final E neutral, absorbing;

		final boolean isAnd = mWrapper.isAnd(formula);

		if (isAnd) {
			neutral = trueTerm;
			absorbing = falseTerm;
		} else {
			neutral = falseTerm;
			absorbing = trueTerm;
		}

		final LinkedHashSet<E> formulas = new LinkedHashSet<>();
		final Iterator<E> iter = mWrapper.getOperands(formula);
		while (iter.hasNext()) {
			final E f = iter.next();

			if (mWrapper.isEqual(f, neutral)) {
				continue;
			}
			if (mWrapper.isEqual(f, absorbing)) {
				return f;
			}

			/* Normalize nested and/ors */
			formulas.addAll(mWrapper.normalizeNesting(formula, f));
		}

		if (formulas.size() <= 1) {
			if (formulas.isEmpty()) {
				return neutral;
			}
			return formulas.iterator().next();
		}

		if (isAnd) {
			return mWrapper.makeAnd(formulas.iterator());
		}
		return mWrapper.makeOr(formulas.iterator());
	}

}
