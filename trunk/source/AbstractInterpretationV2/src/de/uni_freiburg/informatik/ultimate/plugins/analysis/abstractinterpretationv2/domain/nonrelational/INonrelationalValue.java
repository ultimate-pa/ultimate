package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public interface INonrelationalValue<V extends INonrelationalValue<V>> {

	V copy();
	
	boolean isBottom();
	
	V intersect (final V other);
	
	V merge (final V other);
	
	boolean isEqualTo(final V other);
	
	Term getTerm(final Script script, final Sort sort, final Term var);
	
	boolean isContainedIn(final V otherValue);
	
	V add(final V other);
	
	V subtract(final V other);
	
	V multiply(final V other);
	
	V integerDivide(final V other);
	
	V divide(final V other);
	
	V modulo(final V other, final boolean isInteger);
	
	V greaterThan(final V other);

	BooleanValue isGreaterThan(final V other);
	
	V greaterOrEqual(final V other);
	
	BooleanValue isGreaterOrEqual(final V other);
	
	V lessThan(final V other);

	BooleanValue isLessThan(final V other);
	
	V lessOrEqual(final V other);
	
	BooleanValue isLessOrEqual(final V other);
	
	V inverseModulo(final V referenceValue, final V oldValue, final boolean isLeft);
	
	V inverseEquality(final V otherValue, final V oldValue);
	
	V inverseLessOrEqual(final V otherValue, final V oldValue, final boolean isLeft);
	
	V inverseLessThan(final V otherValue, final V oldValue, final boolean isLeft);
	
	V inverseGreaterOrEqual(final V otherValue, final V oldValue, final boolean isLeft);
	
	V inverseGreaterThan(final V otherValue, final V oldValue, final boolean isLeft);
	
	V inverseNotEqual(final V otherValue, final V oldValue);

}
