package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.valuedomain;

public interface IValueOperator<T> {
	public IAbstractValue<T> apply(IAbstractValue<?> valueA,
			IAbstractValue<?> valueB);
}
