package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.normalforms;

import java.util.Collection;
import java.util.Iterator;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 * @param <E>
 */
public interface IConditionWrapper<E> {

	E changeForall(E oldForAll, E operand);

	E makeAnd(E next, E notor);

	Collection<? extends E> normalizeNesting(E formula, E subformula);

	E makeFalse();

	E makeTrue();

	E changeExists(E oldExists, E operand);

	E makeOr(Iterator<E> operands);

	E makeAnd(Iterator<E> operands);

	E makeNot(E operand);

	E getOperand(E formula);
	
	E rewriteNotEquals(E atom);

	Iterator<E> getOperands(E formula);

	boolean isAtom(E formula);

	boolean isNot(E formula);

	boolean isAnd(E formula);

	boolean isOr(E formula);

	boolean isExists(E formula);

	boolean isForall(E formula);

	boolean isEqual(E one, E other);
}