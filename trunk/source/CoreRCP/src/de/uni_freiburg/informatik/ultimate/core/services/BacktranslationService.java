package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.result.IProgramExecution;

/**
 * 
 * @author dietsch
 * 
 */
public class BacktranslationService implements IStorable, IBacktranslationService {

	private static final String sKey = "BacktranslationService";
	private ModelTranslationContainer mTranslatorSequence;

	public BacktranslationService() {
		mTranslatorSequence = new ModelTranslationContainer();
	}

	@Override
	public <STE, TTE, SE, TE> void addTranslator(ITranslator<STE, TTE, SE, TE> translator) {
		mTranslatorSequence.addTranslator(translator);
	}

	@Override
	public <SE> Object translateExpression(SE expression, Class<SE> clazz) {
		return mTranslatorSequence.translateExpression(expression, clazz);
	}

	@Override
	public <STE> List<?> translateTrace(List<STE> trace, Class<STE> clazz) {
		return mTranslatorSequence.translateTrace(trace, clazz);
	}

	@Override
	public <STE, SE> IProgramExecution<?, ?> translateProgramExecution(IProgramExecution<STE, SE> programExecution) {
		return mTranslatorSequence.translateProgramExecution(programExecution);
	}

	@Override
	public <SE> String translateExpressionToString(SE expression, Class<SE> clazz) {
		return mTranslatorSequence.translateExpressionToString(expression, clazz);
	}

	@Override
	public <STE> List<String> translateTraceToString(List<STE> trace, Class<STE> clazz) {
		return mTranslatorSequence.translateTraceToString(trace, clazz);
	}

	@Override
	public IBacktranslationService getTranslationServiceCopy() {
		return mTranslatorSequence.getTranslationServiceCopy();
	}

	static IBacktranslationService getService(IToolchainStorage storage) {
		assert storage != null;
		IStorable rtr = storage.getStorable(sKey);
		if (rtr == null) {
			rtr = new BacktranslationService();
			storage.putStorable(sKey, rtr);
		}
		return (IBacktranslationService) rtr;
	}

	@Override
	public String toString() {
		return mTranslatorSequence.toString();
	}

	@Override
	public void destroy() {
		// TODO: it is unclear if we need to destroy anything in the back
		// translators
	}

}
