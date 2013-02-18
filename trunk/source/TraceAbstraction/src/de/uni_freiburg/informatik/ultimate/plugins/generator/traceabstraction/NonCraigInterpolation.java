package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.io.PrintWriter;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.NaiveDestructiveEqualityResolution;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.NestedSsa;

public class NonCraigInterpolation {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	final Script m_Script;
	final SmtManager m_SmtManager;
	final Smt2Boogie m_BoogieVar2SmtVar;

	final NestedWord<CodeBlock> m_NestedWord;
	final IRun<CodeBlock, IPredicate> m_Run;
	final Set<ProgramPoint> m_cutpoints;
	final PrintWriter m_IterationPW;
	final int m_Iteration;
	
	private IPredicate[] m_Interpolants;
	private LBool m_Satisfiable;

	private TAPreferences m_Pref;
	private NestedSsa m_SSA;

	public NonCraigInterpolation(SmtManager smtManager,
								 	IRun<CodeBlock, IPredicate> run,
								 	NestedSsa nestedSSA,
								 	Set<ProgramPoint> cutpoints,
								 	TAPreferences prefs,
								 	int iteration,
								 	PrintWriter iterationPW) {
		m_Pref = prefs;
		m_Script = smtManager.getScript();
		m_SmtManager = smtManager;
		m_BoogieVar2SmtVar = smtManager.getBoogieVar2SmtVar();
		
		m_NestedWord = NestedWord.nestedWord(run.getWord());
		m_Run = run;
		m_SSA = nestedSSA;
		m_cutpoints = cutpoints;
		assert (m_SSA.getTerms().length+1 == run.getLength());
		m_Iteration = iteration;
		m_IterationPW = iterationPW;
		computeInterpolants();
	}
	
	private void computeInterpolants() {
		m_Interpolants = new IPredicate[m_Run.getLength()];
		m_Interpolants[m_Interpolants.length-1] = m_SmtManager.newFalsePredicate(); 
		for (int i = m_Interpolants.length-2; i>0;i--) {
			TransFormula transFormula = m_Run.getSymbol(i).getTransitionFormula();
			m_Interpolants[i] = weakestPrecondition(m_Interpolants[i+1], transFormula);
		}
		m_Interpolants[0] = m_SmtManager.newTruePredicate(); 
		for (int i=0; i<m_Interpolants.length-1; i++) {
			m_SmtManager.isInductive(m_Interpolants[i], m_Run.getSymbol(i), m_Interpolants[i+1], true);
		}

	}
	

	
	public IPredicate[] getNestedInterpolants() {
		return m_Interpolants;
	}
	
	public LBool isInputSatisfiable() {
		return m_Satisfiable;
	}
	
	private IPredicate weakestPrecondition(IPredicate postState, TransFormula transFormula) {
		Term resFormula = postState.getFormula();
		Set<BoogieVar> resVars = new HashSet<BoogieVar>(postState.getVars());
		
		Map<BoogieVar, TermVariable> inVars = transFormula.getInVars();
		Map<BoogieVar, TermVariable> outVars = transFormula.getOutVars();
		Set<TermVariable> newAuxVars = new HashSet<TermVariable>();
		
//		try {
			for (BoogieVar var : outVars.keySet()) {
				if (inVars.get(var) != outVars.get(var)) {
					if (inVars.get(var) == null) {
						resVars.remove(var);
					}
					newAuxVars.add(outVars.get(var));
					if (postState.getVars().contains(var)) {
						TermVariable[] vars = { var.getTermVariable() };
						Term[] values = { outVars.get(var) };

						resFormula = m_Script.let(vars, values, resFormula);
					}
				}
			}

			resFormula = m_Script.term("and",m_Script.term("not", resFormula),transFormula.getFormula());
			for (BoogieVar var : inVars.keySet()) {
				TermVariable[] vars = { inVars.get(var) };
				Term[] values = { var.getTermVariable() };
				resFormula = m_Script.let(vars, values, resFormula);
				resVars.add(var);
			}
//			TermVariable[] vars = newAuxVars.toArray(new TermVariable[0]);
//			Term [] values = new Term[vars.length];
//			for (int i=0; i<vars.length; i++) {
//				values[i] = m_SmtManager.getConstant(m_Script, vars[i] + "IfrshT" + m_Iteration, vars[i].getSort());
//			}
//			resFormula = m_Script.let(vars, values, resFormula);
		
//		} catch (ölö e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}

		NaiveDestructiveEqualityResolution der = new NaiveDestructiveEqualityResolution(m_Script);

		resFormula = der.eliminate(newAuxVars, resFormula);
		resFormula = m_Script.term("not", resFormula);
		SimplifyDDA sdda = new SimplifyDDA(m_Script, s_Logger);
		resFormula = sdda.getSimplifiedTerm(resFormula);
		
		throw new AssertionError("currently unsupported, implement computation of predicates procedures first");
		// Predicate res = m_PredicateFactory.newPredicate(resFormula, new String[]{"deprecated"},  resVars);
		// return res;
	}
	

	
	
	
}
