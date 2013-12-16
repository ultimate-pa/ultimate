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
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The affine template finds an affine-linear ranking function.
 * 
 * Template:
 * <pre>δ > 0 /\ f(x) > 0 /\ f(x') < f(x) - δ</pre>
 * 
 * @author Jan Leike
 */
public class AffineTemplate extends RankingFunctionTemplate {
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term m_delta;
	private AffineFunctionGenerator m_fgen;
	
	@Override
	public void init(Script script, Collection<BoogieVar> vars) {
		super.init(script, vars);
		m_delta = RankingFunctionTemplate.newDelta(script, s_name_delta);
		m_fgen = new AffineFunctionGenerator(script, vars, s_name_function);
	}
	
	@Override
	public String toString() {
		return "Affine template:\n"
			+ "   delta > 0\n/\\ f(x) >= 0\n/\\ f(x) >= f(x') + delta";
	}
	
	@Override
	public List<List<LinearInequality>> constraints(
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		checkInitialized();
		List<List<LinearInequality>> conjunction =
				new ArrayList<List<LinearInequality>>();
		
		// f(x) > 0
		{
			LinearInequality li = m_fgen.generate(inVars);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			conjunction.add(Collections.singletonList(li));
		}
		
		// f(x') < f(x) - delta
		{
			LinearInequality li = m_fgen.generate(inVars);
			LinearInequality li2 = m_fgen.generate(outVars);
			li2.negate();
			li.add(li2);
			ParameterizedRational p = new ParameterizedRational(m_delta);
			p.coefficient = Rational.MONE;
			li.add(p);
			li.setStrict(true);
			li.needs_motzkin_coefficient = false;
			conjunction.add(Collections.singletonList(li));
		}
		
		// delta > 0 is assured by RankingFunctionTemplate.newDelta
		return conjunction;
	}

	@Override
	public Collection<Term> getVariables() {
		Collection<Term> list = m_fgen.getVariables();
		list.add(m_delta);
		return list;
	}

	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		AffineFunction f = m_fgen.extractAffineFunction(val);
		return new LinearRankingFunction(f);
	}
	
	@Override
	public List<String> getAnnotations() {
		List<String> annotations = new ArrayList<String>();
		annotations.add("rank bounded");
		annotations.add("rank decreasing");
		return annotations;
	}
	
	@Override
	public int getDegree() {
		return 0;
	}
}