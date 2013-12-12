package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Object for all result for which ULTIMATE das not offer a special result class.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <P>
 */
public class GenericResult<P> extends AbstractResult<P> {

	/**
	 * Severity of a result determines how the result is visualized in a 
	 * front end.
	 */
	public enum Severity { ERROR, WARNING, INFO }
	
	private final ILocation m_Location;
	private final String m_ShortDescription;
	private final String m_LongDescription;
	private final Severity m_Severity;
	

	public GenericResult(P position, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence,
			ILocation location, String shortDescription, String longDescription,
			Severity severity) {
		super(position, plugin, translatorSequence);
		m_Location = location;
		m_ShortDescription = shortDescription;
		m_LongDescription = longDescription;
		m_Severity = severity;
	}

	@Override
	public ILocation getLocation() {
		return m_Location;
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
