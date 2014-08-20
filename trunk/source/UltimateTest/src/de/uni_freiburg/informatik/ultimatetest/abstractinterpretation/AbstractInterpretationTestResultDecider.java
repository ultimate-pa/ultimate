/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.abstractinterpretation;

import java.io.File;

import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider;

/**
 * @author Christopher Dillo
 *
 */
public class AbstractInterpretationTestResultDecider extends
		SafetyCheckTestResultDecider {

	/**
	 * @param inputFile
	 */
	public AbstractInterpretationTestResultDecider(File inputFile) {
		super(inputFile);
	}

}
