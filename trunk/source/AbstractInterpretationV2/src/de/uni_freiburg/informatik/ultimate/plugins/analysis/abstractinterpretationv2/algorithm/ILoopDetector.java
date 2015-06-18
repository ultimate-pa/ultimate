package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 * 
 */
public interface ILoopDetector<ACTION> {

	ACTION getLoopExit(ACTION transition);
}
