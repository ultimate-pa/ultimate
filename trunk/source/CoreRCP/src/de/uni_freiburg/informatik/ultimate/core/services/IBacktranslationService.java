package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

/**
 * 
 * {@link IBacktranslationService} contains all {@link ITranslator} instances
 * for the currently running toolchain.
 * 
 * @author dietsch
 * 
 */
public interface IBacktranslationService {

	/**
	 * Add a new translator to the backtranslation service. It has to be
	 * type-compatible with the existing ones!
	 * 
	 * @param translator
	 */
	public <STE, TTE, SE, TE> void addTranslator(ITranslator<STE, TTE, SE, TE> translator);

	public <SE> Object translateExpression(SE expression, Class<SE> clazz);

	public <SE> String translateExpressionToString(SE expression, Class<SE> clazz);

	public <STE> List<?> translateTrace(List<STE> trace, Class<STE> clazz);

	public <STE> List<String> translateTraceToHumanReadableString(List<STE> trace, Class<STE> clazz);

	public <STE, SE> IProgramExecution<?, ?> translateProgramExecution(IProgramExecution<STE, SE> programExecution);

	public IBacktranslationService getTranslationServiceCopy();

}