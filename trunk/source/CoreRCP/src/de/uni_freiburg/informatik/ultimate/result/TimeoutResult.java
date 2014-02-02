package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class TimeoutResult<P extends IElement> extends AbstractResultWithPosition<P> implements IResult{
	
	private final String m_longDescription;


	public TimeoutResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location, 
			String longDescription) {
		super(position, plugin, translatorSequence);
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
