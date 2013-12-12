package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

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
public class SyntaxErrorResult<P> extends AbstractResult<P> implements IResult {
	
	public enum SyntaxErrorType {
		IncorrectSyntax("Incorrect Syntax"), 
		TypeError("Type Error"), 
		UnsupportedSyntax("Unsupported Syntax");
		
		String m_Description;
		
		private SyntaxErrorType(String name) {
			m_Description = name;
		}
		
		public String getDescription() {
			return m_Description;
		}
	};
	
	private final ILocation m_Location;
	private final SyntaxErrorType m_SyntaxErrorType;
	
	private String m_LongDescription;

	/**
	 * @param location
	 * @param syntaxErrorType
	 */
	public SyntaxErrorResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, 
			ILocation location, SyntaxErrorType syntaxErrorType) {
		super(position, plugin, translatorSequence);
		m_Location = location;
		m_SyntaxErrorType = syntaxErrorType;
	}

	@Override
	public ILocation getLocation() {
		return m_Location;
	}

	@Override
	public String getShortDescription() {
		return m_SyntaxErrorType.getDescription();
	}

	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}

	public void setLongDescription(String longDescription) {
		m_LongDescription = longDescription;
	}

	
}