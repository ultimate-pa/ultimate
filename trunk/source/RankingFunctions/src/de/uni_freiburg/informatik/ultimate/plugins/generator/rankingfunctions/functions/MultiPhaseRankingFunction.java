package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;


/**
 * A multiphase ranking function.
 * 
 * @author Jan Leike
 */
public class MultiPhaseRankingFunction implements RankingFunction {
	
	private static final long serialVersionUID = 8644898436783278162L;
	
	private List<LinearRankingFunction> m_rankingFunctions;
	
	public MultiPhaseRankingFunction() {
		m_rankingFunctions = new ArrayList<LinearRankingFunction>();
	}
	
	/**
	 * Set a coefficient for a variable.
	 */
	public void addPhase(LinearRankingFunction rf) {
		m_rankingFunctions.add(rf);
	}
	
	public List<LinearRankingFunction> getPhases() {
		return m_rankingFunctions;
	}
	
	@Override
	public String toString() {
		String result = "";
		for (int i = 0; i < m_rankingFunctions.size(); ++i) {
			LinearRankingFunction rf = m_rankingFunctions.get(i);
			result += "f_" + i;
			result += rf.toString().substring(1);
			result += "\n";
		}
		return result.substring(0, result.length() - 1);
	}
	
	@Override
	public Term asFormula(Script script, Smt2Boogie smt2boogie)
			throws SMTLIBException {
		return null; // TODO
	}
	
	@Override
	public Rational evaluate(Map<BoogieVar, Rational> assignment) {
		// Does not return the phase. Use getPhase() for this.
		Rational r = Rational.ZERO;
		for (LinearRankingFunction rf : m_rankingFunctions) {
			r = rf.evaluate(assignment);
			if (!r.isNegative()) {
				return r;
			}
		}
		return r;
	}
	
	/**
	 * Returns the current phase index
	 * @param assignment variable assignment
	 * @return -1 if last phase has ended
	 */
	public int getPhase(Map<BoogieVar, Rational> assignment) {
		for (int i = 0; i < m_rankingFunctions.size(); ++i) {
			LinearRankingFunction rf = m_rankingFunctions.get(i);
			if (!rf.evaluate(assignment).isNegative()) {
				return i;
			}
		}
		return -1;
	}
}
