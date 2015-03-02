package de.uni_freiburg.informatik.ultimate.witnessparser;

import java.io.File;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * 
 */
public class WitnessAutomatonConstructor {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;

	public WitnessAutomatonConstructor(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}
	
	public IElement constructWitnessAutomaton(File file){
		
		
		
		return null;
	}

}
