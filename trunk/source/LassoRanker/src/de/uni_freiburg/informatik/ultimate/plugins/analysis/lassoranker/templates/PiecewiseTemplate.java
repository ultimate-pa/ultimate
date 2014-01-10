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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.PiecewiseRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The piecewise template finds ranking functions that are piecewise defined
 * functions.
 * 
 * Template:
 * <pre>
 *    /\ δ > 0
 * /\ /\_i /\_j g_i(x) < 0 \/ g_j(x') < 0 \/ f_j(x') < f_i(x) - delta
 * /\ /\_i f_i(x) > 0
 * /\ ( \/_i g_i(x) >= 0 )
 * </pre>
 * 
 * The functions f_i define the pieces.  Each function has a discriminatory
 * predicate g_i() >= 0.  We use this piece iff the corresponding predicate is
 * satisfied.
 * 
 * @author Jan Leike
 */
public class PiecewiseTemplate extends RankingFunctionTemplate {
	
	public final int size;
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	private static final String s_name_pred = "pred";
	
	private Term m_delta;
	private AffineFunctionGenerator[] m_fgens; // functions
	private AffineFunctionGenerator[] m_pgens; // discriminatory predicates
	
	/**
	 * @param num_functions number of lexicographic entries
	 */
	public PiecewiseTemplate(int num_pieces) {
		assert(num_pieces > 0);
		size = num_pieces;
		m_fgens = new AffineFunctionGenerator[size];
		m_pgens = new AffineFunctionGenerator[size];
	}
	
	@Override
	public void init(Script script, Collection<BoogieVar> vars) {
		super.init(script, vars);
		m_delta = RankingFunctionTemplate.newDelta(script, s_name_delta);
		for (int i = 0; i < size; ++i) {
			m_fgens[i] = new AffineFunctionGenerator(script, vars,
					s_name_function + i);
			m_pgens[i] = new AffineFunctionGenerator(script, vars,
					s_name_pred + i);
		}
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(size);
		sb.append("-piece template:\n   ");
		sb.append("   delta > 0\n");
		for (int i = 0; i < size; ++i) {
			for (int j = 0; j < size; ++j) {
				sb.append("/\\ ( g_" + i + "(x) < 0 \\/");
				sb.append("g_" + j + "(x') < 0 \\/");
				sb.append("f_" + j + "(x') < f_" + i + "(x) - delta )\n");
			}
		}
		for (int i = 0; i < size; ++i) {
			sb.append("/\\ f_" + i + "(x) > 0\n");
		}
		sb.append("/\\ ( ");
		for (int i = 0; i < size; ++i) {
			sb.append("g_" + i + "(x) >= 0");
			if (i < size - 1) {
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
		
		// /\_i /\_j g_i(x) < 0 \/ g_j(x') < 0 \/ f_j(x') < f_i(x) - delta
		for (int i = 0; i < size; ++i) {
			for (int j = 0; j < size; ++j) {
				List<LinearInequality> disjunction =
						new ArrayList<LinearInequality>();
				
				LinearInequality li1 = m_pgens[i].generate(inVars);
				li1.negate();
				li1.setStrict(true);
				li1.needs_motzkin_coefficient = i != j;
				disjunction.add(li1);
				
				LinearInequality li2 = m_pgens[j].generate(outVars);
				li2.negate();
				li2.setStrict(true);
				li2.needs_motzkin_coefficient = true;
				disjunction.add(li2);
				
				LinearInequality li3 = m_fgens[i].generate(inVars);
				LinearInequality li4 = m_fgens[j].generate(outVars);
				li4.negate();
				li3.add(li4);
				AffineTerm a = new AffineTerm(m_delta, Rational.MONE);
				li3.add(a);
				li3.setStrict(true);
				li3.needs_motzkin_coefficient = false;
				disjunction.add(li3);
			}
		}
		
		// /\_i f_i(x) > 0
		for (int i = 0; i < size; ++i) {
			LinearInequality li = m_fgens[i].generate(inVars);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			conjunction.add(Collections.singletonList(li));
		}
		
		// \/_i g_i(x) >= 0
		List<LinearInequality> disjunction = new ArrayList<LinearInequality>();
		for (int i = 0; i < size; ++i) {
			LinearInequality li = m_pgens[i].generate(inVars);
			li.setStrict(false);
			li.needs_motzkin_coefficient = i > 0;
			disjunction.add(li);
		}
		conjunction.add(disjunction);
		
		// delta > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public Collection<Term> getVariables() {
		Collection<Term> list = new ArrayList<Term>();
		list.add(m_delta);
		for (int i = 0; i < size; ++i) {
			list.addAll(m_fgens[i].getVariables());
			list.addAll(m_pgens[i].getVariables());
		}
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		List<AffineFunction> fs = new ArrayList<AffineFunction>();
		List<AffineFunction> gs = new ArrayList<AffineFunction>();
		for (int i = 0; i < size; ++i) {
			AffineFunction f = m_fgens[i].extractAffineFunction(val);
			AffineFunction g = m_pgens[i].extractAffineFunction(val);
			fs.add(f);
			gs.add(g);
		}
		return new PiecewiseRankingFunction(fs, gs);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		for (int i = 0; i < size; ++i) {
			for (int j = 0; j < size; ++j) {
				annotations.add("transition from piece " + i + " to piece " + j);
			}
		}
		for (int i = 0; i < size; ++i) {
			annotations.add("rank f" + i + " is bounded");
		}
		annotations.add("case split is exhaustive");
		return annotations;
	}

	@Override
	public int getDegree() {
		assert(size > 0);
		return 2*size*size - 1;
	}
}