package de.uni_freiburg.informatik.ultimate.automata;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public abstract class AbstractOperation<LETTER,STATE> implements IOperation<LETTER,STATE> {

	protected final Logger mLogger;
	protected final IUltimateServiceProvider mServices;
	
	
	protected AbstractOperation(Logger logger, IUltimateServiceProvider services){
		mLogger = logger;
		mServices = services;
	}
	
}
