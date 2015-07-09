package de.uni_freiburg.informatik.ultimate.result;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;

/**
 * Nontermination argument in form of an infinite program execution.
 * 
 * The infinite execution described by this nontermination argument is
 * 
 * <pre>
 * state_init,
 * state_honda,
 * state_honda + ray_1 + ... + ray_n,
 * state_honda + (1 + lambda_1) ray_1 + ... + (1 + lambda_n) ray_n,
 * state_honda + (1 + lambda_1 + lambda_1^2) ray_1 + ... + (1 + lambda_n + lambda_n^2) ray_n,
 * ...
 * </pre>
 * 
 * This implementation nontermination argument is highly tailored to the
 * nontermination arguments that the LassoRanker plugin discovers and is
 * unlikely to be useful anywhere else.
 * 
 * In the long term, it might be desirable to have a more general implementation
 * of a nontermination argument.
 * 
 * @author Jan Leike
 * @param <P> program position class
 */
public class NonTerminationArgumentResult<P extends IElement> extends AbstractResultAtElement<P> implements IResult {
	/**
	 * How many steps the infinite execution should be schematically unwinded
	 */
	private final static int s_schematic_execution_length = 3;

	private final Map<Expression, Rational> m_StateInit;
	private final Map<Expression, Rational> m_StateHonda;
	private final List<Map<Expression, Rational>> m_Rays;
	private final List<Rational> m_Lambdas;

	private final boolean m_AlternativeLongDescription = !false;

	/**
	 * Construct a termination argument result
	 * 
	 * @param position
	 *            program position
	 * @param plugin
	 *            the generating plugin's name
	 * @param ranking_function
	 *            a ranking function as an implicitly lexicographically ordered
	 *            list of Boogie expressions
	 * @param rankingFunctionDescription
	 *            short name of the ranking function
	 * @param supporting_invariants
	 *            list of supporting invariants in form of Boogie expressions
	 * @param translatorSequence
	 *            the toolchain's translator sequence
	 * @param location
	 *            program location
	 */
	public NonTerminationArgumentResult(P position, String plugin,
			Map<Expression, Rational> state_init,
			Map<Expression, Rational> state_honda,
			List<Map<Expression, Rational>> rays,
			List<Rational> lambdas,
			IBacktranslationService translatorSequence) {
		super(position, plugin, translatorSequence);
		this.m_StateInit = state_init;
		this.m_StateHonda = state_honda;
		this.m_Rays = rays;
		this.m_Lambdas = lambdas;
		assert m_Rays.size() == m_Lambdas.size();
	}

	@Override
	public String getShortDescription() {
		return "Nontermination argument in form of an infinite " + "program execution.";
	}

	private String printState(Map<Expression, String> state) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		boolean first = true;
		for (Entry<Expression, String> entry : state.entrySet()) {
			String var = mTranslatorSequence.translateExpressionToString(entry.getKey(), Expression.class);
			if (var.contains("UnsupportedOperation")) {
				continue;
			}
			if (!first) {
				sb.append(", ");
			} else {
				first = false;
			}
			// sb.append(BoogieStatementPrettyPrinter.print(entry.getKey()));
			sb.append(var);
			// sb.append(BackTranslationWorkaround.backtranslate(
			// m_TranslatorSequence, entry.getKey()));
			// TODO: apply backtranslation?
			sb.append("=");
			sb.append(entry.getValue());
		}
		sb.append("}");
		return sb.toString();
	}

	@Override
	public String getLongDescription() {
		if (m_AlternativeLongDescription) {
			return alternativeLongDesciption();
		} else {
			return defaultLongDescription();
		}
	}

	public String defaultLongDescription() {
		StringBuilder sb = new StringBuilder();
		sb.append("Nontermination argument in form of an infinite execution\n");
		sb.append(m_StateInit);
		assert (s_schematic_execution_length > 0);
		Rational[] geometric_sum =
				new Rational[m_Lambdas.size()]; // 1 + lambda + lambda^2 + ...
		for (int i = 0; i < m_Lambdas.size(); ++i) {
			geometric_sum[i] = Rational.ZERO;
		}
		for (int j = 0; j < s_schematic_execution_length; ++j) {
			Map<Expression, String> state = new HashMap<Expression, String>();
			for (Expression var : m_StateHonda.keySet()) {
				Rational x = m_StateHonda.get(var);
				for (int i = 0; i < m_Rays.size(); ++i) {
					Rational y = m_Rays.get(i).get(var);
					Rational lambda = m_Lambdas.get(i);
					if (y != null) {
						x = x.add(y.mul(geometric_sum[i]));
					}
				}
				state.put(var, x.toString());
			}
			for (int i = 0; i < m_Rays.size(); ++i) {
				geometric_sum[i] = geometric_sum[i].mul(m_Lambdas.get(i)).add(Rational.ONE);
			}
			sb.append("\n");
			sb.append(printState(state));
		}
		return sb.toString();
	}

	private String alternativeLongDesciption() {
		StringBuilder sb = new StringBuilder();
		sb.append("Nontermination argument in form of an infinite execution\n");
		sb.append("State at position 0 is\n");
		Map<Expression, String> statePos0 = new HashMap<Expression, String>();
		for (Entry<Expression, Rational> entry : m_StateHonda.entrySet()) {
			Expression var = entry.getKey();
			Rational x0 = m_StateInit.get(var);
			statePos0.put(var, x0.toString());
		}
		sb.append(printState(statePos0));
		sb.append("\nState at position 1 is\n");
		Map<Expression, String> statePos1 = new HashMap<Expression, String>();
		for (Entry<Expression, Rational> entry : m_StateHonda.entrySet()) {
			Expression var = entry.getKey();
			Rational x = m_StateHonda.get(var);
			statePos1.put(var, x.toString());
		}
		sb.append(printState(statePos1));
		sb.append("\nFor i>1, the state at position i is\n");
		Map<Expression, String> statePosI = new HashMap<Expression, String>();
		for (Expression var : m_StateHonda.keySet()) {
			Rational x = m_StateHonda.get(var);
			String value = x.toString();
			for (int i = 0; i < m_Lambdas.size(); ++i) {
				Rational y = m_Rays.get(i).get(var);
				if (y != null && !y.equals(Rational.ZERO)) {
					if (m_Lambdas.get(i).equals(Rational.ONE)) {
						value += " + " + "i * " + y;
					} else {
						value += " + " + geometric(i) + " * " + y;
					}
				}
			}
			statePosI.put(var, value);
		}
		sb.append(printState(statePosI));
		return sb.toString();
	}

	private String geometric(int i) {
		StringBuilder sb = new StringBuilder();
		sb.append("(");
		sb.append(m_Lambdas.get(i));
		sb.append("^(i+1)-1)/(");
		sb.append(m_Lambdas.get(i));
		sb.append("-1)");
		return sb.toString();
	}

}
