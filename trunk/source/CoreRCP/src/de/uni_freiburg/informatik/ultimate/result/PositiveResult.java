package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Result to store that the specification given at some location always holds. 
 * The specification at this location may explicitly (e.g., there is a assert
 * statement at this location) or implicitly (e.g. at this location a pointer is
 * dereferenced and the programming language does not allow dereference of 
 * nullpointers).
 * @author Markus Lindenmann
 * @author Stefan Wissert
 * @author Oleksii Saukh
 * @date 27.03.2012
 */
public class PositiveResult<P extends IElement> extends AbstractResultWithPosition<P> implements IResult {
	private String m_ShortDescription;
	private String m_LongDescription;

	/**
	 * Constructor.
	 * 
	 * @param location
	 *            the location
	 */
	public PositiveResult(P position, String plugin, 
			List<ITranslator<?,?,?,?>> translatorSequence, ILocation location) {
		super(position, plugin, translatorSequence);
		this.m_ShortDescription = new String();
		this.m_LongDescription = new String();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.result.IResultNode#getShortDescription
	 * ()
	 */
	@Override
	public String getShortDescription() {
		return m_ShortDescription;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.result.IResultNode#getLongDescription
	 * ()
	 */
	@Override
	public String getLongDescription() {
		return m_LongDescription;
	}

	/**
	 * Setter for short description.
	 * 
	 * @param shortDescription
	 *            the shortDescription to set
	 */
	public void setShortDescription(String shortDescription) {
		this.m_ShortDescription = shortDescription;
	}

	/**
	 * Setter for long description.
	 * 
	 * @param longDescription
	 *            the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.m_LongDescription = longDescription;
	}
}
