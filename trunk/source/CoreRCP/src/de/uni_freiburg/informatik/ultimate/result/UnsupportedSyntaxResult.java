package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Report that some syntax is not (yet?) supported by our implementation 
 * (e.g. input is program that uses arrays but solver setting uses logic that
 * does not support arrays) .
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class UnsupportedSyntaxResult<ELEM extends IElement> 
						extends AbstractResult implements IResultWithLocation {
	
	private final ELEM m_Position;
	protected final List<ITranslator<?, ?, ?, ?>> m_TranslatorSequence;
	private final ILocation m_Location;
	private String m_LongDescription;

	/**
	 * @param location
	 * @param syntaxErrorType
	 */
	public UnsupportedSyntaxResult(ELEM position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, String longDescription) {
		super(plugin);
		m_Position = position;
		m_TranslatorSequence = translatorSequence;
		m_Location = null;
		m_LongDescription = longDescription;
	}
	
	public UnsupportedSyntaxResult(String plugin, ILocation location,
			String longDescription) {
		super(plugin);
		m_Position = null;
		m_TranslatorSequence = null;
		m_Location = location;
		m_LongDescription = longDescription;
	}

	@Override
	public String getShortDescription() {
		return "Unsupported Syntax";
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}
	
	public final ILocation getLocation() {
		assert ((m_Position == null) ^ (m_Location == null)) : 
			"exactly one has to be non-null";
		if (m_Position != null) {
			return m_Position.getPayload().getLocation();
		} else {
			return m_Location;
		}
	}

	public final ELEM getElement() {
		return m_Position;
	}

	
}