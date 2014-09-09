package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;

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
			IBacktranslationService translatorSequence, 
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

	@Override
	public Severity getSeverity() {
		return m_Severity;
	}

}
