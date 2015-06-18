package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 * 
 */
public interface IResultReporter {

	//TODO: Define this interface -- how do we create counter example?
	
	void reportPossibleError();

	void reportSafe();
}
