package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
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
	protected final List<ITranslator<?, ?, ?, ?>> m_TranslatorSequence;
	
	public AbstractResultAtElement(ELEM element, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence) {
		super(plugin);
		m_Element = element;
		m_TranslatorSequence = translatorSequence;
	}
	
	public final ILocation getLocation() {
		return m_Element.getPayload().getLocation();
	}

	public final ELEM getElement() {
		return m_Element;
	}


}
