/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.core.services.model.ILogger;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.Nnf.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.models.IElement;
import de.uni_freiburg.informatik.ultimate.models.IPayload;
import de.uni_freiburg.informatik.ultimate.models.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.models.structure.ModifiableAST;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;

/**
 * Specifies properties of a state in a graph representation of a system. These
 * properties are
 * <ul>
 * <li>Name of a location m_LocationName</li>
 * <li>Name of a procedure m_ProcedureName</li>
 * <li>Possible valuations of variables in this state m_StateFormulas</li>
 * </ul>
 * 
 * @author heizmann@informatik.uni-freiburg.de
 */

public class HoareAnnotation extends SPredicate {

	//DD: Matthias, do you really want to save only one annotation?
	private static final String KEY = Activator.s_PLUGIN_ID;
	private static final long serialVersionUID = 72852101509650437L;
	
	private final ILogger mLogger;
	private final IUltimateServiceProvider m_Services;

	private final Script m_Script;
	private final Boogie2SMT m_Boogie2Smt;
	private final PredicateFactory m_PredicateFactory;
	private final ModifiableGlobalVariableManager m_ModifiableGlobals;

	private final Map<Term, Term> m_Precondition2Invariant = new HashMap<Term, Term>();
	private boolean m_IsUnknown = false;

	private boolean m_FormulaHasBeenComputed = false;
	private Term m_ClosedFormula;
	private static final boolean s_AvoidImplications = true;
	

	public HoareAnnotation(ProgramPoint programPoint, int serialNumber, 
			Boogie2SMT boogie2smt, PredicateFactory predicateFactory, 
			ModifiableGlobalVariableManager modifiableGlobals, 
			IUltimateServiceProvider services) {
		super(programPoint, serialNumber, new String[] { programPoint.getProcedure() }, boogie2smt.getScript().term(
				"true"), new HashSet<BoogieVar>(), null);
		mLogger = services.getLoggingService().getLogger(Activator.s_PLUGIN_ID);
		m_Services = services;
		m_Boogie2Smt = boogie2smt;
		m_PredicateFactory = predicateFactory;
		m_Script = boogie2smt.getScript();
		m_ModifiableGlobals = modifiableGlobals;
	}

	/**
	 * The published attributes. Update this and getFieldValue() if you add new
	 * attributes.
	 */
	private final static String[] s_AttribFields = { "ProgramPoint", "StateIsUnknown", "Formula", "Vars",
			"Precondition2InvariantMapping", "Precondition2InvariantMappingAsStrings" };

	@Override
	protected String[] getFieldNames() {
		return s_AttribFields;
	}

	@Override
	protected Object getFieldValue(String field) {
		if (field == "Precondition2InvariantMapping")
			return m_Precondition2Invariant;
		else if (field == "StateIsUnknown")
			return m_IsUnknown;
		else if (field == "Precondition2InvariantMappingAsStrings")
			return getPrecondition2InvariantMappingAsStrings();
		else
			return super.getFieldValue(field);
	}

	public void addInvariant(IPredicate procPrecond, IPredicate locInvar) {
		if (m_FormulaHasBeenComputed) {
			throw new UnsupportedOperationException("Once Formula has been"
					+ " computed it is not allowed to add new Formulas");
		}
		if (m_PredicateFactory.isDontCare(procPrecond) || m_PredicateFactory.isDontCare(locInvar)) {
			this.m_IsUnknown = true;
			return;
		}
		m_Vars.addAll(procPrecond.getVars());
		m_Vars.addAll(locInvar.getVars());
		Term procPrecondFormula = procPrecond.getFormula();
		// procPrecondFormula = (new SimplifyDDA(m_Script,
		// s_Logger)).getSimplifiedTerm(procPrecondFormula);
		Term locInvarFormula = locInvar.getFormula();
		Term invarForPrecond = m_Precondition2Invariant.get(procPrecondFormula);
		if (invarForPrecond == null) {
			invarForPrecond = locInvarFormula;
		} else {
			invarForPrecond = Util.and(m_Script, invarForPrecond, locInvarFormula);
		}
		// invarForPrecond = (new SimplifyDDA(m_Script,
		// s_Logger)).getSimplifiedTerm(invarForPrecond);
		// procPrecondFormula = (new SimplifyDDA(m_Script,
		// s_Logger)).getSimplifiedTerm(procPrecondFormula);
		m_Precondition2Invariant.put(procPrecondFormula, invarForPrecond);
	}

	@Override
	public Term getFormula() {
		if (!m_FormulaHasBeenComputed) {
			computeFormula();
			m_FormulaHasBeenComputed = true;
		}
		return m_Formula;
	}
	
	@Override
	public Term getClosedFormula() {
		if (!m_FormulaHasBeenComputed) {
			computeFormula();
			m_FormulaHasBeenComputed = true;
		}
		return m_ClosedFormula;
	}

	private void computeFormula() {
		for (Term precond : getPrecondition2Invariant().keySet()) {
			Term invariant = getPrecondition2Invariant().get(precond);
			invariant = SmtUtils.simplify(m_Script, invariant, m_Services); 
			Term precondTerm = Util.implies(m_Script, precond, invariant);
			if (s_AvoidImplications) {
				precondTerm = (new Nnf(m_Script, m_Services, m_Boogie2Smt.getVariableManager(), QuantifierHandling.KEEP)).transform(precondTerm);
			}
			mLogger.debug("In " + this + " holds " + invariant + " for precond " + precond);
			m_Formula = Util.and(m_Script, m_Formula, precondTerm);
		}
		m_Formula = substituteOldVarsOfNonModifiableGlobals(getProgramPoint().getProcedure(), m_Vars,
				m_Formula);
		m_Formula = SmtUtils.simplify(m_Script, m_Formula, m_Services); 
		m_Formula = getPositiveNormalForm(m_Formula);
		TermVarsProc tvp = TermVarsProc.computeTermVarsProc(m_Formula, m_Boogie2Smt);
		m_ClosedFormula = PredicateUtils.computeClosedFormula(tvp.getFormula(), tvp.getVars(), m_Script);
	}
	
	
	/**
	 * For each oldVar in vars that is not modifiable by procedure proc:
	 * substitute the oldVar by the corresponding globalVar in term and remove
	 * the oldvar from vars.
	 */
	public Term substituteOldVarsOfNonModifiableGlobals(String proc, Set<BoogieVar> vars, Term term) {
		final Set<BoogieVar> oldVarsOfmodifiableGlobals = m_ModifiableGlobals.getOldVarsAssignment(proc)
				.getAssignedVars();
		List<BoogieVar> replacedOldVars = new ArrayList<BoogieVar>();

		ArrayList<TermVariable> replacees = new ArrayList<TermVariable>();
		ArrayList<Term> replacers = new ArrayList<Term>();

		for (BoogieVar bv : vars) {
			if (bv instanceof BoogieOldVar) {
				if (!oldVarsOfmodifiableGlobals.contains(bv)) {
					replacees.add(bv.getTermVariable());
					replacers.add((((BoogieOldVar) bv).getNonOldVar()).getTermVariable());
					replacedOldVars.add(bv);
				}
			}
		}

		TermVariable[] substVars = replacees.toArray(new TermVariable[replacees.size()]);
		Term[] substValues = replacers.toArray(new Term[replacers.size()]);
		Term result = m_Script.let(substVars, substValues, term);
		result = (new FormulaUnLet()).unlet(result);

		for (BoogieVar bv : replacedOldVars) {
			vars.remove(bv);
			vars.add(((BoogieOldVar) bv).getNonOldVar());
		}
		return result;
	}
	

	private Term getPositiveNormalForm(Term term) {
		Script script = m_Script;
		Term result = (new AffineSubtermNormalizer(m_Script, mLogger)).transform(term);
		assert (Util.checkSat(script, script.term("distinct", term, result)) != LBool.SAT);
		return result;
	}

	/**
	 * @return the m_FormulaMapping
	 */
	public Map<Term, Term> getPrecondition2Invariant() {
		return m_Precondition2Invariant;
	}

	@Override
	public boolean isUnknown() {
		return m_IsUnknown;
	}

	public Map<String, String> getPrecondition2InvariantMappingAsStrings() {
		HashMap<String, String> result = new HashMap<String, String>();
		for (Entry<Term, Term> entry : m_Precondition2Invariant.entrySet()) {
			result.put(entry.getKey().toStringDirect(), entry.getValue().toStringDirect());
		}
		return result;
	}
	
	public void annotate(IElement node) {
		if (node instanceof ProgramPoint) {
			annotate((ProgramPoint) node);
		}
	}

	public void annotate(ProgramPoint node) {
		node.getPayload().getAnnotations().put(KEY, this);
	}

	public static HoareAnnotation getAnnotation(IElement node) {
		if (node instanceof ProgramPoint) {
			return getAnnotation((ProgramPoint) node);
		}
		return null;
	}

	public static HoareAnnotation getAnnotation(ProgramPoint node) {
		if (node.hasPayload()) {
			final IPayload payload = node.getPayload();
			if (payload.hasAnnotation()) {
				final IAnnotations annot = payload.getAnnotations().get(KEY);
				if (annot != null) {
					return (HoareAnnotation) annot;
				}
			}
		}
		return null;
	}

}
