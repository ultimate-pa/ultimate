package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Class to describe one of the following results
 * <ul>
 * <li> we have detected a syntax error 
 * <li> we have detected a type error (e.g. an int value was assigned to a
 *  Boolean variable)
 * <li> we have detected syntax which is not (yet) supported by out tool or not
 * supported in a specific setting (e.g. input is program that uses arrays but
 * solver setting uses logic that does not support arrays) 
 * </ul>
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class UnsupportedSyntaxResult<P extends IElement> extends AbstractResult implements IResult {
	
	private final P m_Position;
	protected final List<ITranslator<?, ?, ?, ?>> m_TranslatorSequence;
	private final ILocation m_Location;
	private String m_LongDescription;

	/**
	 * @param location
	 * @param syntaxErrorType
	 */
	public UnsupportedSyntaxResult(P position, String plugin, 
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

	public final P getPosition() {
		return m_Position;
	}

	
}