package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.DefaultTranslator;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;


/**
 * Result that reports that a nonterminating execution for a lasso shaped
 * sequence of statements has been found.
 * 
 * @author Matthias Heizmann
 *
 * @param <P>
 */
public class NonterminatingLassoResult<P> extends AbstractResultWithLasso<P> {
	
	private final ILocation m_Location;

	public NonterminatingLassoResult(P position, String plugin,
			List<ITranslator<?, ?, ?, ?>> translatorSequence,
			IProgramExecution<P, ?> stem, IProgramExecution<P, ?> loop,
			ILocation location) {
		super(position, plugin, translatorSequence, stem, loop);
		m_Location = location;
	}

	@Override
	public ILocation getLocation() {
		return m_Location;
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
		sb.append(DefaultTranslator.translateProgramExecutionIteratively(m_Stem, 
				m_TranslatorSequence.toArray(new ITranslator[0])));
		sb.append("Loop:");
		sb.append(System.getProperty("line.separator"));
		sb.append(DefaultTranslator.translateProgramExecutionIteratively(m_Loop, 
				m_TranslatorSequence.toArray(new ITranslator[0])));
		sb.append("End of lasso representation.");
		return sb.toString();
	}

}
