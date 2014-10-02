package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;

/**
 * Result that reports that a nonterminating execution for a lasso shaped
 * sequence of statements has been found.
 * 
 * @author Matthias Heizmann
 * 
 * @param <TE>
 */
public class NonterminatingLassoResult<ELEM extends IElement, TE extends IElement, EXP extends IElement> extends
		AbstractResultWithLasso<ELEM, TE, EXP> {

	public NonterminatingLassoResult(ELEM position, String plugin, IBacktranslationService translatorSequence,
			IProgramExecution<TE, EXP> stem, IProgramExecution<TE, EXP> loop, ILocation location) {
		super(plugin, position, translatorSequence, stem, loop);
	}

	@Override
	public String getShortDescription() {
		return "Nonterminating execution";
	}

	@Override
	public String getLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append("Found a nonterminating execution for the following lasso shaped sequence of statements.");
		sb.append(System.getProperty("line.separator"));
		sb.append("Stem:");
		sb.append(System.getProperty("line.separator"));
		sb.append(m_TranslatorSequence.translateProgramExecution(m_Stem));
		sb.append("Loop:");
		sb.append(System.getProperty("line.separator"));
		sb.append(m_TranslatorSequence.translateProgramExecution(m_Loop));
		sb.append("End of lasso representation.");
		return sb.toString();
	}
}
