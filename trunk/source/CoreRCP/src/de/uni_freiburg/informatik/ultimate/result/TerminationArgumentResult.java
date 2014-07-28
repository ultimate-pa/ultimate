package de.uni_freiburg.informatik.ultimate.result;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;


/**
 * Termination Argument consisting of a ranking function given as a list
 * of lexicographically ordered Boogie expressions.
 * 
 * @author Matthias Heizmann, Jan Leike
 * @param <P> program position class
 */
public class TerminationArgumentResult<P extends IElement> extends AbstractResultAtElement<P>
		implements IResult {
	private final String m_RankingFunctionDescription;
	private final Expression[] m_RankingFunction;
	private final Expression[] m_SupportingInvariants;
	
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
	 */
	public TerminationArgumentResult(P position, String plugin,
			Expression[] ranking_function,
			String rankingFunctionDescription,
			Expression[] supporting_invariants,
			List<ITranslator<?,?,?,?>> translatorSequence) {
		super(position, plugin, translatorSequence);
		this.m_RankingFunction = ranking_function;
		this.m_RankingFunctionDescription = rankingFunctionDescription;
		this.m_SupportingInvariants = supporting_invariants;
	}
	
	@Override
	public String getShortDescription() {
		return "Found " + m_RankingFunctionDescription + " ranking function";
	}
	
	@Override
	public String getLongDescription() {
		StringBuilder sb =  new StringBuilder();
		sb.append("Found a termination argument consisting of the ");
		sb.append(m_RankingFunctionDescription);
		sb.append(" ranking function");
		sb.append(": [");
		sb.append(ResultUtil.backtranslationWorkaround(
				m_TranslatorSequence, m_RankingFunction));
		sb.append("]");
		if (m_SupportingInvariants.length > 0) {
			sb.append(" and the following supporting invariants: ");
			sb.append(ResultUtil.backtranslationWorkaround(
					m_TranslatorSequence, m_SupportingInvariants));
		} else {
			sb.append(" for which no supporting invariant is required.");
		}
		return sb.toString();
	}

	public String getRankingFunctionDescription() {
		return m_RankingFunctionDescription;
	}

	public Expression[] getRankingFunction() {
		return m_RankingFunction;
	}

	public Expression[] getSupportingInvariants() {
		return m_SupportingInvariants;
	}
	
	

}
