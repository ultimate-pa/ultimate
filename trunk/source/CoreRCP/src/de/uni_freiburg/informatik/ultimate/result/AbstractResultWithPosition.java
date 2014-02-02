package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Superclass of all results. Defines the minimal data that a result needs.
 * @author Matthias Heizmann
 *
 * @param <P> Type of node of the ultimate model at which this result was
 * 		obtained.
 */
public abstract class AbstractResultWithPosition<P extends IElement> 
						extends AbstractResult implements IResultWithLocation {
	
	private final P m_Position;
	protected final List<ITranslator<?, ?, ?, ?>> m_TranslatorSequence;
	
	public AbstractResultWithPosition(P position, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence) {
		super(plugin);
		m_Position = position;
		m_TranslatorSequence = translatorSequence;
	}
	
	public final ILocation getLocation() {
		return m_Position.getPayload().getLocation();
	}

	public final P getPosition() {
		return m_Position;
	}


}
