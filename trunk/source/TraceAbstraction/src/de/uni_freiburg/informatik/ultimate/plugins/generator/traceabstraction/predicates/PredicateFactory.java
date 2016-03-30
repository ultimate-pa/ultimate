/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicateExplicitQuantifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BuchiPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.HoareAnnotation;
import de.uni_freiburg.informatik.ultimate.witnessparser.graph.WitnessNode;

public class PredicateFactory {

	private final Boogie2SMT m_Boogie2Smt;
	private final Script m_Script;

	protected int m_SerialNumber;

	private static final Set<BoogieVar> EMPTY_VARS = Collections.emptySet();
	private static final String[] NO_PROCEDURE = new String[0];

	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	protected Term m_DontCareTerm;
	protected Term m_EmptyStackTerm;
	
	
	
	public Term getDontCareTerm() {
		return m_DontCareTerm;
	}

	public PredicateFactory(IUltimateServiceProvider services, Boogie2SMT boogie2smt) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_DontCareTerm = new AuxilliaryTerm("don't care");
		m_EmptyStackTerm = new AuxilliaryTerm("emptyStack");
		m_Boogie2Smt = boogie2smt;
		m_Script = boogie2smt.getScript();
	}
	
	/**
	 * Constructs a predicate from the given term. If the given term is
	 * quantifier-free, a BasicPredicate will be constructed, otherwise it
	 * constructs a BasicPredicateExplicitQuantifier.
	 * 
	 * @param term
	 *            - resulting predicate is constructed using this term
	 * @param quantifier
	 *            - describes how the given variables in the set
	 *            "quantifiedVariables" are quantified (only two possibilities
	 *            here: 0 or 1)
	 * @param quantifiedVariables
	 *            - the variables in the given term, which should be quantified.
	 *            If this set is empty, nothing is quantified, and the result is
	 *            a BasicPredicate, otherwise it constructs a
	 *            BasicPredicateExplicitQuantifier.
	 */
	public IPredicate constructPredicate(Term term, int quantifier, Set<TermVariable> quantifiedVariables) {
		assert checkIfValidPredicate(term, quantifiedVariables);
		if (quantifiedVariables == null || quantifiedVariables.isEmpty()) {
			// Compute the set of BoogieVars, the procedures and the term
			TermVarsProc tvp = TermVarsProc.computeTermVarsProc(term, m_Boogie2Smt);
			return newPredicate(tvp);
		} else {
			Term result = PartialQuantifierElimination.quantifier(m_Services, m_Logger, m_Script, m_Boogie2Smt.getVariableManager(), quantifier,
					quantifiedVariables, term, (Term[][]) null);
			// Compute the set of BoogieVars, the procedures and the term
			TermVarsProc tvp = TermVarsProc.computeTermVarsProc(result, m_Boogie2Smt);
			// Check whether the result has still quantifiers
			if (result instanceof QuantifiedFormula) {
				quantifiedVariables = new HashSet<TermVariable>(Arrays.asList(((QuantifiedFormula) result)
						.getVariables()));
				return new BasicPredicateExplicitQuantifier(m_SerialNumber++, tvp.getProcedures(), result,
						tvp.getVars(), tvp.getClosedFormula(), quantifier, quantifiedVariables);
			} else {
				return newPredicate(tvp);
			}

		}
	}
	
	/**
	 * Returns true iff each free variables corresponds to a BoogieVar or will
	 * be quantified. Throws an Exception otherwise.
	 */
	private boolean checkIfValidPredicate(Term term, Set<TermVariable> quantifiedVariables) {
		for (TermVariable tv : term.getFreeVars()) {
			BoogieVar bv = m_Boogie2Smt.getBoogie2SmtSymbolTable().getBoogieVar(tv);
			if (bv == null) {
				if (!quantifiedVariables.contains(tv)) {
					throw new AssertionError("Variable " + tv + " does not corresponds to a BoogieVar, and is"
							+ " not quantified, hence this formula cannot" + " define a predicate: " + term);
				}
			}
		}
		return true;
	}

	public static HoareAnnotation getHoareAnnotation(ProgramPoint programPoint) {
		return HoareAnnotation.getAnnotation(programPoint);
	}

	public PredicateWithHistory newPredicateWithHistory(ProgramPoint pp, TermVarsProc tvp, Map<Integer, Term> history) {
		PredicateWithHistory pred = new PredicateWithHistory(pp, m_SerialNumber++, tvp.getProcedures(), tvp.getFormula(), tvp.getVars(),
				tvp.getClosedFormula(), history);
		return pred;
	}

	public boolean isDontCare(IPredicate pred) {
		return pred.getFormula() == m_DontCareTerm;
	}
	
	public boolean isDontCare(TermVarsProc tvp) {
		return tvp.getFormula() == m_DontCareTerm;
	}

	public SPredicate newSPredicate(ProgramPoint pp, TermVarsProc termVarsProc) {
		SPredicate pred = new SPredicate(pp, m_SerialNumber++, termVarsProc.getProcedures(), termVarsProc.getFormula(),
				termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return pred;
	}

	public BasicPredicate newPredicate(TermVarsProc termVarsProc) {
		BasicPredicate predicate = new BasicPredicate(m_SerialNumber++, termVarsProc.getProcedures(),
				termVarsProc.getFormula(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return predicate;
	}

	public MLPredicate newMLPredicate(ProgramPoint[] programPoints, TermVarsProc termVarsProc) {
		MLPredicate predicate = new MLPredicate(programPoints, m_SerialNumber++, termVarsProc.getProcedures(),
				termVarsProc.getFormula(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return predicate;
	}
	
	public ProdState getNewProdState(List<IPredicate> programPoints) {
		return new ProdState(m_SerialNumber++, programPoints, m_Script.term("true"),new HashSet<BoogieVar>(0));
	}
	
	public TermVarsProc constructTrue() {
		final Term trueTerm = m_Script.term("true");
		return new TermVarsProc(trueTerm, EMPTY_VARS, NO_PROCEDURE, trueTerm);
	}
	
	public TermVarsProc constructFalse() {
		final Term trueTerm = m_Script.term("false");
		return new TermVarsProc(trueTerm, EMPTY_VARS, NO_PROCEDURE, trueTerm);
	}
	
	public TermVarsProc constructDontCare() {
		return new TermVarsProc(m_DontCareTerm, EMPTY_VARS, NO_PROCEDURE, m_DontCareTerm);
	}

	
	

	public UnknownState newDontCarePredicate(ProgramPoint pp) {
		UnknownState pred = new UnknownState(pp, m_SerialNumber++, m_DontCareTerm);
		return pred;
	}

	public DebugPredicate newDebugPredicate(String debugMessage) {
		DebugPredicate pred = new DebugPredicate(debugMessage, m_SerialNumber++, m_DontCareTerm);
		return pred;
	}

	public ISLPredicate newEmptyStackPredicate() {
		ProgramPoint pp = new ProgramPoint("noCaller", "noCaller", false, null);
		return newSPredicate(pp, new TermVarsProc(m_EmptyStackTerm, EMPTY_VARS, NO_PROCEDURE, m_EmptyStackTerm));

	}

	public SPredicate newTrueSLPredicateWithWitnessNode(ProgramPoint pp, WitnessNode witnessNode, Integer stutteringSteps) {
		SPredicate pred = new SPredicateWithWitnessNode(pp, m_SerialNumber++, NO_PROCEDURE, m_Script.term("true"), EMPTY_VARS,
				m_Script.term("true"), witnessNode, stutteringSteps);
		return pred;
	}

	public HoareAnnotation getNewHoareAnnotation(ProgramPoint pp, ModifiableGlobalVariableManager modifiableGlobals) {
		return new HoareAnnotation(pp, m_SerialNumber++, m_Boogie2Smt, this, modifiableGlobals, m_Services);
	}

	public IPredicate newBuchiPredicate(Set<IPredicate> inputPreds) {
		TermVarsProc tvp = and(inputPreds.toArray(new IPredicate[0]));
		BuchiPredicate buchi = new BuchiPredicate(m_SerialNumber++, tvp.getProcedures(), tvp.getFormula(),
				tvp.getVars(), tvp.getClosedFormula(), inputPreds);
		return buchi;
	}
	
	
	
	public TermVarsProc and(IPredicate... preds) {
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		Set<String> procs = new HashSet<String>();
		Term term = m_Script.term("true");
		for (IPredicate p : preds) {
			if (isDontCare(p)) {
				return new TermVarsProc(m_DontCareTerm, EMPTY_VARS, NO_PROCEDURE, m_DontCareTerm);
			}
			vars.addAll(p.getVars());
			procs.addAll(Arrays.asList(p.getProcedures()));
			term = Util.and(m_Script, term, p.getFormula());
		}
		Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, m_Script);
		return new TermVarsProc(term, vars, procs.toArray(new String[0]), closedTerm);
	}
	
	public TermVarsProc or(IPredicate... preds) {
		return or(false, preds);
	}
	
	public TermVarsProc orWithSimplifyDDA(IPredicate... preds) {
		return or(true, preds);
	}

	public TermVarsProc or(boolean withSimplifyDDA, IPredicate... preds) {
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		Set<String> procs = new HashSet<String>();
		Term term = m_Script.term("false");
		for (IPredicate p : preds) {
			if (isDontCare(p)) {
				return new TermVarsProc(m_DontCareTerm, EMPTY_VARS, NO_PROCEDURE, m_DontCareTerm);
			}
			vars.addAll(p.getVars());
			procs.addAll(Arrays.asList(p.getProcedures()));
			term = Util.or(m_Script, term, p.getFormula());
		}
		if (withSimplifyDDA) {
			term = SmtUtils.simplify(m_Script, term, m_Services);
		}
		Term closedTerm = PredicateUtils.computeClosedFormula(term, vars, m_Script);
		return new TermVarsProc(term, vars, procs.toArray(new String[0]), closedTerm);
	}

	public TermVarsProc not(IPredicate p) {
		if (isDontCare(p)) {
			return new TermVarsProc(m_DontCareTerm, EMPTY_VARS, NO_PROCEDURE, m_DontCareTerm);
		}
		Term term = Util.not(m_Script, p.getFormula());
		Term closedTerm = Util.not(m_Script, p.getClosedFormula());
		return new TermVarsProc(term, p.getVars(), p.getProcedures(), closedTerm);
	}
	

	

	
	private class AuxilliaryTerm extends Term {

		String m_Name;

		private AuxilliaryTerm(String name) {
			super(0);
			m_Name = name;
		}

		@Override
		public Sort getSort() {
			throw new UnsupportedOperationException("Auxiliary term has no sort");
		}

		@Override
		public void toStringHelper(ArrayDeque<Object> m_Todo) {
			throw new UnsupportedOperationException("Auxiliary term must not be subterm of other terms");
		}

		@Override
		public TermVariable[] getFreeVars() {
			throw new UnsupportedOperationException("Auxiliary term has no vars");
		}

		@Override
		public Theory getTheory() {
			throw new UnsupportedOperationException("Auxiliary term has no theory");
		}

		@Override
		public String toString() {
			return m_Name;
		}

		@Override
		public String toStringDirect() {
			return m_Name;
		}

		@Override
		public int hashCode() {
			throw new UnsupportedOperationException("Auxiliary term must not be contained in any collection");
		}
	}


}
