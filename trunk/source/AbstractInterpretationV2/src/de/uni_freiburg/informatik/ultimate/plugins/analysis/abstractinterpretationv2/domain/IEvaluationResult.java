package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

/**
 * Interface type that is returned by every call of {@link IEvaluator#evaluate(IAbstractState)} of an {@link IEvaluator}
 * .
 * 
 * @author greitsch@informatik.uni-freiburg.de
 *
 * @param <T>
 *            Any type.
 */
public interface IEvaluationResult<T> {

	public T getResult();
}
