package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * Class to represent a type error that has been found. 
 * (e.g. an int value was assigned to a  Boolean variable)
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TypeErrorResult<ELEM extends IElement> extends 
				AbstractResultAtElement<ELEM> implements IResultWithLocation {
	
	private final String m_LongDescription;

	public TypeErrorResult(ELEM element, String plugin, 
			IBacktranslationService translatorSequence, 
			String longDescription) {
		super(element, plugin, translatorSequence);
		m_LongDescription = longDescription;
	}

	@Override
	public String getShortDescription() {
		return "Type Error";
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}
	
}