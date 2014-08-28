package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;

/**
 * 
 * {@link IBacktranslationService} contains all {@link ITranslator} instances
 * for the currently running toolchain.
 * 
 * 
 * 
 * @author dietsch
 * 
 */
public interface IBacktranslationService {

	/**
	 * 
	 * @return
	 */
	public abstract List<ITranslator<?, ?, ?, ?>> getTranslatorSequence();

}