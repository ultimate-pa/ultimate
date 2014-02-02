package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

/**
 * Object for all results for which ULTIMATE does not offer a special result class.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <P>
 */
public class GenericResultAtElement<P extends IElement> 
		extends AbstractResultAtElement<P> implements IResultWithSeverity {

	private final String m_ShortDescription;
	private final String m_LongDescription;
	private final Severity m_Severity;
	

	public GenericResultAtElement(P position, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence, 
			String shortDescription, String longDescription,
			Severity severity) {
		super(position, plugin, translatorSequence);
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
