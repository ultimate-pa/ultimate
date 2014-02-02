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
public class TypeErrorResult<P extends IElement> extends AbstractResultWithPosition<P> implements IResult {
	
	private String m_LongDescription;

	/**
	 * @param location
	 * @param syntaxErrorType
	 */
	public TypeErrorResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence) {
		super(position, plugin, translatorSequence);
	}

	@Override
	public String getShortDescription() {
		return "Type Error";
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}

	public void setLongDescription(String longDescription) {
		m_LongDescription = longDescription;
	}

	
}