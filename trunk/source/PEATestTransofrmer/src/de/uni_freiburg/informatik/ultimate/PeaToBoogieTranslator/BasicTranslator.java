package de.uni_freiburg.informatik.ultimate.PeaToBoogieTranslator;

import pea.PhaseEventAutomata;

/**
 * This is a basic PEA to Boogie translator.
 * This class handles the direct tanslation to boogie while the PeaToBoogiePreparation handles the
 * extraction of the required data from the peas themselves.
 * @author langenfv@informatik.uni-freiburg.de
 *
 */
public class BasicTranslator {
	
	protected PhaseEventAutomata[] peas;

	public BasicTranslator(PhaseEventAutomata[] peas){
		this.peas = peas;
	}
	
}
