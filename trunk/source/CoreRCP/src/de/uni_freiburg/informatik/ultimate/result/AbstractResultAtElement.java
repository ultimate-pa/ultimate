package de.uni_freiburg.informatik.ultimate.result;


import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Superclass of all results that are reported for a specific element.
 * @author Matthias Heizmann
 *
 * @param <ELEM> Type of node of the ultimate model at which this result was
 * 		obtained.
 */
public abstract class AbstractResultAtElement<ELEM extends IElement> 
						extends AbstractResult implements IResultWithLocation {
	
	private final ELEM m_Element;
	protected final IBacktranslationService m_TranslatorSequence;
	
	public AbstractResultAtElement(ELEM element, String plugin,
			IBacktranslationService translatorSequence) {
		super(plugin);
		m_Element = element;
		m_TranslatorSequence = translatorSequence.getTranslationServiceCopy();
	}
	
	public final ILocation getLocation() {
		return m_Element.getPayload().getLocation();
	}

	public final ELEM getElement() {
		return m_Element;
	}


}
