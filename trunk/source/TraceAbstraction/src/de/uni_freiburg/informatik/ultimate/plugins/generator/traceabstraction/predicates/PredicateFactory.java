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
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BasicPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.BuchiPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
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
	private final ILogger m_Logger;
	
	protected Term m_DontCareTerm;
	protected Term m_EmptyStackTerm;
	
	
	
	public Term getDontCareTerm() {
		return m_DontCareTerm;
	}

	public PredicateFactory(IUltimateServiceProvider services, Boogie2SMT boogie2smt) {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		m_DontCareTerm = new AuxilliaryTerm("don't care");
		m_EmptyStackTerm = new AuxilliaryTerm("emptyStack");
		m_Boogie2Smt = boogie2smt;
		m_Script = boogie2smt.getScript();
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

	public PredicateWithHistory newPredicateWithHistory(ProgramPoint pp, Term term, Map<Integer, Term> history) {
		final TermVarsProc tvp = constructTermVarsProc(term);
		PredicateWithHistory pred = new PredicateWithHistory(pp, m_SerialNumber++, tvp.getProcedures(), tvp.getFormula(), tvp.getVars(),
				tvp.getClosedFormula(), history);
		return pred;
	}

	public boolean isDontCare(IPredicate pred) {
		return pred.getFormula() == m_DontCareTerm;
	}
	
	public boolean isDontCare(Term term) {
		return term == m_DontCareTerm;
	}

	public SPredicate newSPredicate(ProgramPoint pp, final Term term) {
		final TermVarsProc termVarsProc = constructTermVarsProc(term);
		return newSPredicate(pp, termVarsProc);
	}
	
	private SPredicate newSPredicate(ProgramPoint pp, final TermVarsProc termVarsProc) {
		SPredicate pred = new SPredicate(pp, m_SerialNumber++, termVarsProc.getProcedures(), termVarsProc.getFormula(),
				termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return pred;
	}

	public BasicPredicate newPredicate(final Term term) {
		final TermVarsProc termVarsProc = constructTermVarsProc(term);
		BasicPredicate predicate = new BasicPredicate(m_SerialNumber++, termVarsProc.getProcedures(),
				termVarsProc.getFormula(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return predicate;
	}

	private TermVarsProc constructTermVarsProc(final Term term) {
		final TermVarsProc termVarsProc;
		if (term == m_DontCareTerm) {
			termVarsProc = constructDontCare();
		} else {
			termVarsProc = TermVarsProc.computeTermVarsProc(term, m_Boogie2Smt);
		}
		return termVarsProc;
	}

	public MLPredicate newMLPredicate(ProgramPoint[] programPoints, Term term) {
		final TermVarsProc termVarsProc = constructTermVarsProc(term);
		MLPredicate predicate = new MLPredicate(programPoints, m_SerialNumber++, termVarsProc.getProcedures(),
				termVarsProc.getFormula(), termVarsProc.getVars(), termVarsProc.getClosedFormula());
		return predicate;
	}
	
	public ProdState getNewProdState(List<IPredicate> programPoints) {
		return new ProdState(m_SerialNumber++, programPoints, m_Script.term("true"),new HashSet<BoogieVar>(0));
	}
	
	private TermVarsProc constructDontCare() {
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
		final Term conjunction = and(inputPreds);
		final TermVarsProc tvp = TermVarsProc.computeTermVarsProc(conjunction, m_Boogie2Smt);
		BuchiPredicate buchi = new BuchiPredicate(m_SerialNumber++, tvp.getProcedures(), tvp.getFormula(),
				tvp.getVars(), tvp.getClosedFormula(), inputPreds);
		return buchi;
	}
	
	
	
	public Term and(IPredicate... preds) {
		return and(Arrays.asList(preds));
	}
	
	public Term and(Collection<IPredicate> preds) {
		Term term = m_Script.term("true");
		for (IPredicate p : preds) {
			if (isDontCare(p)) {
				return m_DontCareTerm;
			}
			term = Util.and(m_Script, term, p.getFormula());
		}
		return term;
	}
	
	public Term or(boolean withSimplifyDDA, IPredicate... preds) {
		return or(withSimplifyDDA, Arrays.asList(preds));
	}

	public Term or(boolean withSimplifyDDA, Collection<IPredicate> preds) {
		Term term = m_Script.term("false");
		for (IPredicate p : preds) {
			if (isDontCare(p)) {
				return m_DontCareTerm;
			}
			term = Util.or(m_Script, term, p.getFormula());
		}
		if (withSimplifyDDA) {
			term = SmtUtils.simplify(m_Script, term, m_Services);
		}
		return term;
	}

	public Term not(IPredicate p) {
		if (isDontCare(p)) {
			return m_DontCareTerm;
		}
		Term term = SmtUtils.not(m_Script, p.getFormula());
		return term;
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
