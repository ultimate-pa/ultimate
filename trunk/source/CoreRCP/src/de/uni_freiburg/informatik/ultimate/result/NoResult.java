package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;

public class NoResult<P extends IElement> extends AbstractResultAtElement<P> implements IResult {
	private String shortDescription;
	private String longDescription;

	/**
	 * Constructor.
	 * @param valuation
	 *            the valuation
	 */
	public NoResult(P position, String plugin, 
			IBacktranslationService translatorSequence) {
		super(position, plugin, translatorSequence);
		this.shortDescription = new String();
		this.longDescription = new String();
	}

	/**
	 * Setter for short description.
	 * 
	 * @param shortDescription
	 *            the shortDescription to set
	 */
	public void setShortDescription(String shortDescription) {
		this.shortDescription = shortDescription;
	}

	/**
	 * Setter for long description.
	 * 
	 * @param longDescription
	 *            the longDescription to set
	 */
	public void setLongDescription(String longDescription) {
		this.longDescription = longDescription;
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
		return shortDescription;
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
		return this.longDescription;
	}


}
