package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain;

public interface IAbstractOperator<T> {
	IAbstractState<T> apply(IAbstractState<T> a, IAbstractState<T> b);
}
