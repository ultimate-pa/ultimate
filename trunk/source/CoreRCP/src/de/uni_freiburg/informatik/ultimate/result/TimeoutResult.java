package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

public class TimeoutResult<P> extends AbstractResult<P> implements IResult{
	
	
	private final ILocation m_Location;
	private final String m_longDescription;


	public TimeoutResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location, 
			String longDescription) {
		super(position, plugin, translatorSequence);
		this.m_Location = location;
		this.m_longDescription = longDescription;
	}
	
	@Override
	public ILocation getLocation() {
		return m_Location;
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
