package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.io.IOException;
import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearTransition;
import de.uni_freiburg.informatik.ultimate.lassoranker.SMTSolver;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.AddAxioms;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.DNF;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.MatchInVars;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RemoveNegation;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteBooleans;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteDivision;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteEquality;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteIte;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteStrictInequalities;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.RewriteTrueFalse;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.SimplifyPreprocessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.TransformerPreProcessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors.TransitionPreProcessor;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.MotzkinTransformation;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.LassoPartitioneer;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.TransFormulaLR;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;

public class DefaultInvariantPatternProcessor implements
		IInvariantPatternProcessor {

	private Script m_script;
	private IUltimateServiceProvider m_Services;
	private IToolchainStorage m_Storage;
	private String filename = null;
	/**
	 * Command for Z3.
	 */
	public String smt_solver_command = "z3 -smt2 -in SMTLIB2_COMPLIANT=true -t:42000";
	private ReplacementVarFactory replacementVarFactory;
	private Script m_RcfgScript;
	private Term[] m_axioms;

	@Override
	public Term getInvariantPatternForLocation(Location location, int round) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Map<TermVariable, ConstantTerm> getValidConfiguration(
			Collection<InvariantTransitionPredicate> predicates, int round) {

		
		try {
			m_script = SMTSolver.newScript(true, smt_solver_command, filename , false, m_Services, m_Storage);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
		MotzkinTransformation mt = new MotzkinTransformation(m_script, AnalysisType.Nonlinear, false);
		Collection<LinearInequality> linearInequalities = null;
		mt.add_inequalities(linearInequalities);
		mt.transform(new Rational[0]);
		
		m_script.reset();
		m_script.setLogic(Logics.QF_NRA);
		// construct new 0-ary function symbol
		m_script.declareFun("coefficient", new Sort[0], m_script.sort("Real"));
		// statt dessen lieber
		Term zeroary = SMTSolver.newConstant(m_script, "coefficient", "Real");
		Term t1 = null;
		Term t2 = null;
		m_script.term("and", t1, t2);
		Util.and(m_script, t1, t2);
		m_script.term("<=", t1, t2);
		SmtUtils.leq(m_script, t1, t2);
		
		Term contraint = null;
		m_script.assertTerm(contraint);
		LBool sat = m_script.checkSat();
		switch (sat) {
		case SAT: {
			// extract values
			Collection<Term> coefficientsOfAllInvariants = null;
			Map<Term, Term> val = m_script.getValue(coefficientsOfAllInvariants.toArray(new Term[coefficientsOfAllInvariants.size()]));
		}
		break;
		case UNKNOWN:
		case UNSAT:
		default:
			break;
		}
		
		
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public int getMaxRounds() {
		// TODO Auto-generated method stub
		return 0;
	}
	


}
