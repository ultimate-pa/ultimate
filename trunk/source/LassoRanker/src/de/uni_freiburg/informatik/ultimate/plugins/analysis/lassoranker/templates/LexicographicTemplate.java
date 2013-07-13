package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.ParameterizedRational;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.LexicographicRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The multiphase template finds ranking functions that proceed through a
 * fixed number of phases where each phase is ranked by an affine-linear
 * function.
 * 
 * Template:
 * <pre>
 *    /\_i δ_i > 0
 * /\ /\_i f_i(x) > 0
 * /\ ( /\_(i < k) f_i(x') ≤ f_i(x) \/ \/_(j<i) f_j(x') < f_j(x) - δ_j )
 * /\ ( \/_i f_i(x') < f_i(x) - δ_i )
 * </pre>
 * 
 * @author Jan Leike
 */
public class LexicographicTemplate extends RankingFunctionTemplate {
	
	public final int lex;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term[] m_deltas;
	private AffineFunctionGenerator[] m_fgens;
	
	/**
	 * @param num_functions number of lexicographic entries
	 */
	public LexicographicTemplate(int num_lex) {
		assert(num_lex > 0);
		lex = num_lex;
		m_deltas = new Term[lex];
		m_fgens = new AffineFunctionGenerator[lex];
	}
	
	@Override
	public void init(Script script, Collection<BoogieVar> vars) {
		super.init(script, vars);
		for (int i = 0; i < lex; ++i) {
			m_deltas[i] = RankingFunctionTemplate.newDelta(script,
					s_name_delta + i);
			m_fgens[i] = new AffineFunctionGenerator(script, vars,
					s_name_function + i);
		}
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(lex);
		sb.append("-lex template:\n   ");
		for (int i = 0; i < lex; ++i) {
			sb.append("delta_" + i + " > 0\n/\\ ");
		}
		for (int i = 0; i < lex; ++i) {
			sb.append("f_" + i + "(x) > 0\n/\\ ");
		}
		for (int i = 0; i < lex - 1; ++i) {
			sb.append("( f_" + i + "(x') <= f_" + i + "(x)");
			for (int j = i - 1; j >= 0; --j) {
				sb.append(" \\/ f_" + j + "(x') < f_" + j + "(x) - delta_" + j);
			}
			sb.append(" )\n/\\ ");
		}
		sb.append("( ");
		for (int i = 0; i < lex; ++i) {
			sb.append("f_" + i + "(x') < f_" + i + "(x) - delta_" + i);
			if (i < lex - 1) {
				sb.append(" \\/ ");
			}
		}
		sb.append(" )");
		return sb.toString();
	}
	
	@Override
	public List<List<LinearInequality>> constraints(
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		checkInitialized();
		List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// /\_i f_i(x) > 0
		for (int i = 0; i < lex; ++i) {
			LinearInequality li = m_fgens[i].generate(inVars);
			li.strict = true;
			li.needs_motzkin_coefficient = false;
			conjunction.add(Collections.singletonList(li));
		}
		
		// /\_(i < k) f_i(x') ≤ f_i(x) \/ \/_(j<i) f_j(x') < f_j(x) - δ_j
		for (int i = 0; i < lex - 1; ++i) {
			List<LinearInequality> disjunction =
					new ArrayList<LinearInequality>();
			LinearInequality li = m_fgens[i].generate(inVars);
			LinearInequality li2 = m_fgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			li.strict = false;
			li.needs_motzkin_coefficient = false;
			disjunction.add(li);
			
			for (int j = i - 1; j >= 0; --j) {
				li = m_fgens[j].generate(inVars);
				LinearInequality li3 = m_fgens[j].generate(outVars);
				li3.negate();
				li.add(li3);
				ParameterizedRational p =
						new ParameterizedRational(m_deltas[j]);
				p.coefficient = Rational.MONE;
				li.add(p);
				li.strict = true;
				li.needs_motzkin_coefficient = j > 0;
				disjunction.add(li);
			}
			conjunction.add(disjunction);
		}
		
		// \/_i f_i(x') < f_i(x) - δ_i
		List<LinearInequality> disjunction = new ArrayList<LinearInequality>();
		for (int i = 0; i < lex; ++i) {
			LinearInequality li = m_fgens[i].generate(inVars);
			LinearInequality li2 = m_fgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			ParameterizedRational p = new ParameterizedRational(m_deltas[i]);
			p.coefficient = Rational.MONE;
			li.add(p);
			li.strict = true;
			li.needs_motzkin_coefficient = i > 0 && i < lex - 1;
			disjunction.add(li);
		}
		conjunction.add(disjunction);
		
		// delta_i > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public Collection<Term> getVariables() {
		Collection<Term> list = new ArrayList<Term>();
		for (int i = 0; i < lex; ++i) {
			list.addAll(m_fgens[i].getVariables());
			list.add(m_deltas[i]);
		}
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		List<AffineFunction> fs = new ArrayList<AffineFunction>();
		for (int i = 0; i < lex; ++i) {
			AffineFunction f = m_fgens[i].extractAffineFunction(val);
			fs.add(f);
		}
		return new LexicographicRankingFunction(fs);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		for (int i = 0; i < lex; ++i) {
			annotations.add("rank f" + i + " is bounded");
		}
		for (int i = 0; i < lex - 1; ++i) {
			annotations.add("rank f" + i + " is not increasing unless "
					+ "a smaller index decreases");
		}
		annotations.add("at least one rank index decreases");
		return annotations;
	}

	@Override
	public int getDegree() {
		assert(lex > 0);
		return (lex - 1)*(lex - 2) / 2;
	}
}