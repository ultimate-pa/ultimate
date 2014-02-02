package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

/**
 * Superclass of all Results that refer to a lasso shaped infinite execution. 
 * @author Matthias Heizmann
 */
public abstract class AbstractResultWithLasso<P extends IElement> 
										extends AbstractResultAtElement<P> {
	protected final IProgramExecution<P, ?> m_Stem;
	protected final IProgramExecution<P, ?> m_Loop;
	
	public AbstractResultWithLasso(P position, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence,
			IProgramExecution<P, ?> stem, IProgramExecution<P, ?> loop) {
		super(position, plugin, translatorSequence);
		m_Stem = stem;
		m_Loop = loop;
	}
	
	


}
