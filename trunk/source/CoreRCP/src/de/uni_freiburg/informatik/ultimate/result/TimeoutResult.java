package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

/**
 * Use this to report that there was a timeout.
 * The ELEM of this object is a node in the Ultimate model that is related to
 * the problem that was analyzed when this timeout occurred.
 * @author Matthias Heizmann
 *
 * @param <ELEM>
 */
public class TimeoutResult<ELEM extends IElement> 
					extends AbstractResultAtElement<ELEM> implements IResult{
	
	private final String m_longDescription;


	public TimeoutResult(ELEM element, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, String longDescription) {
		super(element, plugin, translatorSequence);
		this.m_longDescription = longDescription;
	}
	
	@Override
	public String getShortDescription() {
		return "Timeout";
	}

	@Override
	public String getLongDescription() {
		return m_longDescription;
	}

	
}
