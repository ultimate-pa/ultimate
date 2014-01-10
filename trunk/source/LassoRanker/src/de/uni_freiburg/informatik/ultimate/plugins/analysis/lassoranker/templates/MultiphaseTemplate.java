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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.MultiphaseRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The multiphase template finds ranking functions that proceed through a
 * fixed number of phases where each phase is ranked by an affine-linear
 * function.
 * 
 * Template:
 * <pre>
 *    /\_i δ_i > 0
 * /\ ( \/_i f_i(x) > 0 )
 * /\ ( /\_i (f_i(x') < f_i(x) - δ_i \/ \/_(j<i) f_j(x) > 0 )
 * </pre>
 * 
 * @author Jan Leike
 */
public class MultiphaseTemplate extends RankingFunctionTemplate {
	
	public final int size;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term[] m_deltas;
	private AffineFunctionGenerator[] m_fgens;
	
	/**
	 * @param num_phases number of phases in the multiphase template
	 */
	public MultiphaseTemplate(int num_phases) {
		assert(num_phases > 0);
		size = num_phases;
		m_deltas = new Term[size];
		m_fgens = new AffineFunctionGenerator[size];
	}
	
	@Override
	public void init(Script script, Collection<BoogieVar> vars) {
		super.init(script, vars);
		for (int i = 0; i < size; ++i) {
			m_deltas[i] = RankingFunctionTemplate.newDelta(script,
					s_name_delta + i);
			m_fgens[i] = new AffineFunctionGenerator(script, vars,
					s_name_function + i);
		}
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(size);
		sb.append("-phase template:\n   ");
		for (int i = 0; i < size; ++i) {
			sb.append("delta_" + i + " > 0\n/\\ ");
		}
		sb.append("( ");
		for (int i = 0; i < size; ++i) {
			sb.append("f_" + i + "(x) > 0");
			if (i < size - 1) {
				sb.append(" \\/ ");
			}
		}
		sb.append(" )\n");
		for (int i = 0; i < size; ++i) {
			sb.append("/\\ ( f_" + i + "(x') < f_" + i + "(x) - delta_" + i);
			for (int j = i - 1; j >= 0; --j) {
				sb.append(" \\/ f_" + j + "(x) > 0");
			}
			sb.append(" )\n");
		}
		return sb.toString();
	}
	
	@Override
	public List<List<LinearInequality>> constraints(
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		checkInitialized();
		List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// \/_i f_i(x) > 0
		List<LinearInequality> disjunction =
				new ArrayList<LinearInequality>();
		for (int i = 0; i < size; ++i) {
			LinearInequality li = m_fgens[i].generate(inVars);
			li.setStrict(true);
			li.needs_motzkin_coefficient = i > 0;
			disjunction.add(li);
		}
		conjunction.add(disjunction);
		
		// /\_i ( f_i(x') < f_i(x) - δ_i \/ \/_(j<i) f_j(x) > 0 )
		for (int i = 0; i < size; ++i) {
			disjunction = new ArrayList<LinearInequality>();
			LinearInequality li = m_fgens[i].generate(inVars);
			LinearInequality li2 = m_fgens[i].generate(outVars);
			li2.negate();
			li.add(li2);
			AffineTerm a = new AffineTerm(m_deltas[i], Rational.MONE);
			li.add(a);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			disjunction.add(li);
			
			for (int j = i - 1; j >= 0; --j) {
				LinearInequality li3 = m_fgens[j].generate(inVars);
				li3.setStrict(true);
				li3.needs_motzkin_coefficient = j > 0;
				disjunction.add(li3);
			}
			conjunction.add(disjunction);
		}
		
		// delta_i > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public Collection<Term> getVariables() {
		Collection<Term> list = new ArrayList<Term>();
		for (int i = 0; i < size; ++i) {
			list.addAll(m_fgens[i].getVariables());
			list.add(m_deltas[i]);
		}
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		List<AffineFunction> fs = new ArrayList<AffineFunction>();
		for (int i = 0; i < size; ++i) {
			AffineFunction f = m_fgens[i].extractAffineFunction(val);
			fs.add(f);
		}
		return new MultiphaseRankingFunction(fs);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		annotations.add("at least one rank f_i is bounded");
		for (int i = 0; i < size; ++i) {
			annotations.add("rank f" + i + " is decreasing in phase " + i);
		}
		return annotations;
	}
	
	@Override
	public int getDegree() {
		assert(size > 0);
		return size*(size - 1) / 2;
	}
}