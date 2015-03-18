package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.ModelExtractionUtils;
import de.uni_freiburg.informatik.ultimate.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.MotzkinTransformation;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;

public class DefaultInvariantPatternProcessor implements
		IInvariantPatternProcessor<Collection<Collection<LinearInequality>>> {

	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	private final Script m_Script;
	
	

	public DefaultInvariantPatternProcessor(IUltimateServiceProvider services,
			Script script) {
		super();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Script = script;
	}

	@Override
	public Collection<Collection<LinearInequality>> getInvariantPatternForLocation(Location location, int round) {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public boolean findValidConfiguration(
			Collection<InvariantTransitionPredicate<Collection<Collection<LinearInequality>>>> predicates, int round) {

		reinitializeSolver(m_Script);
		
		MotzkinTransformation mt = new MotzkinTransformation(m_Script, AnalysisType.Nonlinear, false);
		Collection<LinearInequality> linearInequalities = null;
		mt.add_inequalities(linearInequalities);
		mt.transform(new Rational[0]);
		

		// construct new 0-ary function symbol
		m_Script.declareFun("coefficient", new Sort[0], m_Script.sort("Real"));
		// statt dessen lieber
		Term zeroary = SmtUtils.buildNewConstant(m_Script, "coefficient", "Real");
		Term t1 = null;
		Term t2 = null;
		m_Script.term("and", t1, t2);
		Util.and(m_Script, t1, t2);
		m_Script.term("<=", t1, t2);
		SmtUtils.leq(m_Script, t1, t2);
		
		Term contraint = null;
		m_Script.assertTerm(contraint);
		LBool sat = m_Script.checkSat();
		switch (sat) {
		case SAT: {
			// extract values
			Collection<Term> coefficientsOfAllInvariants = null;
			Map<Term, Rational> valuation;
			boolean simplifiedValuation = false;
			try {
				if (simplifiedValuation) {
					valuation = ModelExtractionUtils.getSimplifiedAssignment(
							m_Script, coefficientsOfAllInvariants, m_Logger);
				} else {
					valuation = ModelExtractionUtils.getValuation(
							m_Script, coefficientsOfAllInvariants);
				}
			} catch (TermException e) {
				e.printStackTrace();
				throw new AssertionError("model extraction failed");
			}
		}
		break;
		case UNKNOWN:
		case UNSAT:
		default:
			break;
		}
		
		
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public int getMaxRounds() {
		throw new UnsupportedOperationException("not implemented");
	}

	@Override
	public IPredicate applyConfiguration(
			Collection<Collection<LinearInequality>> pattern) {
		throw new UnsupportedOperationException("not implemented");
	}
	
	
	/**
	 * Reset solver and initialize it afterwards.
	 * For initializing, we set the option produce-models to true 
	 * (this allows us to obtain a satisfying assignment) and we set the 
	 * logic to QF_NRA (nonlinear real arithmetic).
	 * TODO: Matthias unsat cores might be helpful for debugging.
	 */
	private void reinitializeSolver(Script script) {
		script.reset();
		script.setOption(":produce-models", true);
		boolean someExtendedDebugging = false;
		if (someExtendedDebugging ) {
			script.setOption(":produce-unsat-cores", true);
		}
		script.setLogic(Logics.QF_NRA);
	}
	

	


}
