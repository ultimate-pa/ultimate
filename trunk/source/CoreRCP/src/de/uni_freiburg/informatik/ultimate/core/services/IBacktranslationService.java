package de.uni_freiburg.informatik.ultimate.core.services;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;

public interface IBacktranslationService {

	public abstract List<ITranslator<?, ?, ?, ?>> getTranslatorSequence();

}