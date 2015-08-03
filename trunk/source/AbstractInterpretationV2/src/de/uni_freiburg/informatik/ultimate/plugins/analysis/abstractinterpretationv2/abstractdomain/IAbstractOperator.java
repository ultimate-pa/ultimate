package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationV2.abstractdomain;

public interface IAbstractOperator<T>
{
	IAbstractState<T> apply(IAbstractState<T> a, IAbstractState<T> b);
}
