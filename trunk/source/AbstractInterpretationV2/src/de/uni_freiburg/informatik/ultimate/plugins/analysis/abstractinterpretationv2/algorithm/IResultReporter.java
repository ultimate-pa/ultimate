package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

public interface IResultReporter {

	//TODO: Define this interface -- how do we create counter example?
	
	void reportPossibleError();

	void reportSafe();

}
