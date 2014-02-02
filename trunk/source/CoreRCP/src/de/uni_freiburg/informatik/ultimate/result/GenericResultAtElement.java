package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

/**
 * Object for all results for which ULTIMATE does not offer a special result class.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <ELEM>
 */
public class GenericResultAtElement<ELEM extends IElement> 
		extends AbstractResultAtElement<ELEM> implements IResultWithSeverity {

	private final String m_ShortDescription;
	private final String m_LongDescription;
	private final Severity m_Severity;
	

	public GenericResultAtElement(ELEM element, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence, 
			String shortDescription, String longDescription,
			Severity severity) {
		super(element, plugin, translatorSequence);
		m_ShortDescription = shortDescription;
		m_LongDescription = longDescription;
		m_Severity = severity;
	}

	@Override
	public String getShortDescription() {
		return m_ShortDescription;
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}

	public Severity getSeverity() {
		return m_Severity;
	}

}
