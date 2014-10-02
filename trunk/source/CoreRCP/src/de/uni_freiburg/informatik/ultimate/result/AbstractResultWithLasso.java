package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * Superclass of all Results that refer to a lasso shaped infinite execution. 
 * @author Matthias Heizmann
 */
public abstract class AbstractResultWithLasso<ELEM extends IElement, TE extends IElement, EXP extends IElement> 
										extends AbstractResultAtElement<ELEM> {
	protected final IProgramExecution<TE, EXP> m_Stem;
	protected final IProgramExecution<TE, EXP> m_Loop;
	
	public AbstractResultWithLasso(String plugin, ELEM position,
			IBacktranslationService translatorSequence,
			IProgramExecution<TE, EXP> stem, IProgramExecution<TE, EXP> loop) {
		super(position, plugin, translatorSequence);
		m_Stem = stem;
		m_Loop = loop;
	}
	
	


}
