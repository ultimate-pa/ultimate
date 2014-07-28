package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;

//TODO: Comments
public class BacktranslationService implements IStorable, IBacktranslationService {

	private static final String sKey = "BacktranslationService";
	private List<ITranslator<?, ?, ?, ?>> mTranslatorSequence;

	public BacktranslationService() {
		mTranslatorSequence = new ArrayList<ITranslator<?, ?, ?, ?>>();
	}

	@Override
	public List<ITranslator<?, ?, ?, ?>> getTranslatorSequence() {
		return mTranslatorSequence;
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
		// TODO: it is unclear if we need to destory anything in the back
		// translators
	}
}
