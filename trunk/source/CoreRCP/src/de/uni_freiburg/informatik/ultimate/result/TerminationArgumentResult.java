package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;


/**
 * Termination Argument consisting of a ranking function given as a list
 * of lexicographically ordered Boogie expressions.
 * 
 * @author Matthias Heizmann, Jan Leike
 * @param <P> program position class
 */
public class TerminationArgumentResult<P extends IElement> extends AbstractResultAtElement<P>
		implements IResult {
	private final Expression[] m_RankingFunction;
	private final Expression[] m_SupportingInvariants;
	private final String m_RankingFunctionDescription;
	
	/**
	 * Construct a termination argument result
	 * @param position program position
	 * @param plugin the generating plugin's name
	 * @param ranking_function a ranking function as an implicitly
	 *                         lexicographically ordered list of Boogie
	 *                         expressions 
	 * @param rankingFunctionDescription short name of the ranking function
	 * @param supporting_invariants list of supporting invariants in form of
	 *                              Boogie expressions
	 * @param translatorSequence the toolchain's translator sequence
	 * @param location program location
	 */
	public TerminationArgumentResult(P position, String plugin,
			Expression[] ranking_function,
			String rankingFunctionDescription,
			Expression[] supporting_invariants,
			List<ITranslator<?,?,?,?>> translatorSequence,
			ILocation location) {
		super(position, plugin, translatorSequence);
		this.m_RankingFunction = ranking_function;
		this.m_RankingFunctionDescription = rankingFunctionDescription;
		this.m_SupportingInvariants = supporting_invariants;
	}
	
	@Override
	public String getShortDescription() {
		return "Found " + m_RankingFunctionDescription;
	}
	
	@Override
	public String getLongDescription() {
		StringBuilder sb =  new StringBuilder();
		sb.append("Found a termination argument consisting of the ");
		sb.append(m_RankingFunctionDescription);
		sb.append(": [");
		for (int i = 0; i < m_RankingFunction.length; ++i) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append(BackTranslationWorkaround.backtranslate(
					m_TranslatorSequence, m_RankingFunction[i]));
		}
		sb.append("] and the following supporting invariants: ");
		for (int i = 0; i < m_SupportingInvariants.length; ++i) {
			if (i > 0) {
				sb.append(", ");
			}
			sb.append(BackTranslationWorkaround.backtranslate(
					m_TranslatorSequence, m_SupportingInvariants[i]));
		}
		return sb.toString();
	}

}
