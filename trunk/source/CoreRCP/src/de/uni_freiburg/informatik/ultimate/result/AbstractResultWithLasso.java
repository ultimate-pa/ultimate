package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;

/**
 * Superclass of all Results that refer to a lasso shaped infinite execution. 
 * @author Matthias Heizmann
 */
public abstract class AbstractResultWithLasso<ELEM extends IElement> 
										extends AbstractResultAtElement<ELEM> {
	protected final IProgramExecution<ELEM, ?> m_Stem;
	protected final IProgramExecution<ELEM, ?> m_Loop;
	
	public AbstractResultWithLasso(String plugin, ELEM position,
			List<ITranslator<?, ?, ?, ?>> translatorSequence,
			IProgramExecution<ELEM, ?> stem, IProgramExecution<ELEM, ?> loop) {
		super(position, plugin, translatorSequence);
		m_Stem = stem;
		m_Loop = loop;
	}
	
	


}
