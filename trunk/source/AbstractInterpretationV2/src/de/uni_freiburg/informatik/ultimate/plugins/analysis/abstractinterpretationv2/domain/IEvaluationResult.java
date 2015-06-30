package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain;

public interface IEvaluationResult<T> {

	public T getResult();
	
	public void setResult(T value);
}
