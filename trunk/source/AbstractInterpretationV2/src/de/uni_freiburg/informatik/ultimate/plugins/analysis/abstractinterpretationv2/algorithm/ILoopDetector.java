package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

public interface ILoopDetector<ACTION> {

	ACTION getLoopExit(ACTION transition);
	
}
