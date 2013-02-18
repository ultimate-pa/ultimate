package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;

public abstract class AbstractResult<P> implements IResult {
	
	final protected P m_Position;
	final protected String m_Plugin; 
	final protected List<ITranslator<?, ?, ?, ?>> m_TranslatorSequence;
	
	
	
	public AbstractResult(P position, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence) {
		super();
		m_Position = position;
		m_Plugin = plugin;
		m_TranslatorSequence = translatorSequence;
	}

	public P getPosition() {
		return m_Position;
	}


}
