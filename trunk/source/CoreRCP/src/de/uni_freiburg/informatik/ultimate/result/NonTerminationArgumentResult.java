package de.uni_freiburg.informatik.ultimate.result;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ITranslator;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.location.ILocation;


/**
 * Nontermination argument in form of an infinite program execution.
 * 
 * The infinite execution described by this nontermination argument is
 * 
 * state_init, state_honda,
 * state_honda + ray, state_honda + (1 + lambda) ray,
 * state_honda + (1 + lambda + lambda^2) ray, ... 
 * 
 * This implementation nontermination argument is highly tailored to the
 * nontermination arguments that the LassoRanker plugin discovers and is
 * unlikely to be useful anywhere else.
 * 
 * In the long term, it might be desirable to have a more general
 * implementation of a nontermination argument.
 * 
 * @author Jan Leike
 * @param <P> program position class
 */
public class NonTerminationArgumentResult<P extends IElement> extends AbstractResultAtElement<P>
		implements IResult {
	/**
	 * How many steps the infinite execution should be schematically unwinded
	 */
	private final static int s_schematic_execution_length = 3;
	
	private final Map<BoogieVar, Rational> m_StateInit;
	private final Map<BoogieVar, Rational> m_StateHonda;
	private final Map<BoogieVar, Rational> m_Ray;
	private final Rational m_Lambda;
	
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
	public NonTerminationArgumentResult(P position, String plugin,
			Map<BoogieVar, Rational> state_init,
			Map<BoogieVar, Rational> state_honda,
			Map<BoogieVar, Rational> ray,
			Rational lambda,
			List<ITranslator<?,?,?,?>> translatorSequence) {
		super(position, plugin, translatorSequence);
		this.m_StateInit = state_init;
		this.m_StateHonda = state_honda;
		this.m_Ray = ray;
		this.m_Lambda = lambda;
	}
	
	@Override
	public String getShortDescription() {
		return "Nontermination argument in form of an infinite " +
				"program execution.";
	}
	
	private String printState(Map<BoogieVar, Rational> state) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		boolean first = true;
		for (Entry<BoogieVar, Rational> entry : state.entrySet()) {
			if (!first) {
				sb.append(", ");
			} else {
				first = false;
			}
			sb.append(entry.getKey());
//			sb.append(BackTranslationWorkaround.backtranslate(
//					m_TranslatorSequence, entry.getKey()));
			// TODO: apply backtranslation?
			sb.append("=");
			sb.append(entry.getValue());
		}
		sb.append("}");
		return sb.toString();
	}
	
	@Override
	public String getLongDescription() {
		StringBuilder sb =  new StringBuilder();
		sb.append("Nontermination argument in form of an infinite execution\n");
		sb.append(m_StateInit);
		assert(s_schematic_execution_length > 0);
		Rational geometric_sum = Rational.ZERO; // 1 + lambda + lambda^2 + ...
		for (int i = 0; i < s_schematic_execution_length; ++i) {
			Map<BoogieVar, Rational> state =
					new HashMap<BoogieVar, Rational>();
			for (Entry<BoogieVar, Rational> entry : m_StateHonda.entrySet()) {
				BoogieVar var = entry.getKey();
				Rational x = m_StateHonda.get(var);
				Rational y = m_Ray.get(var);
				state.put(var, x.add(y.mul(geometric_sum)));
			}
			sb.append("\n");
			sb.append(printState(state));
			geometric_sum = geometric_sum.mul(m_Lambda).add(Rational.ONE);
		}
		return sb.toString();
	}

}
