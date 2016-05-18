/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.relation.HashRelation;

/**
 * Write a Hoare annotation provided by HoareAnnotationFragments to the CFG.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationWriter {

	private final RootAnnot m_rootAnnot;
	private final SmtManager m_SmtManager;
	private final HoareAnnotationFragments m_HoareAnnotationFragments;

	/**
	 * What is the precondition for a context? Strongest postcondition or entry
	 * given by automaton?
	 */
	private final boolean m_UseEntry;
	private final PredicateTransformer m_PredicateTransformer;

	public HoareAnnotationWriter(RootAnnot rootAnnot, SmtManager smtManager,
			HoareAnnotationFragments hoareAnnotationFragments, IUltimateServiceProvider services) {
		this.m_rootAnnot = rootAnnot;
		this.m_SmtManager = smtManager;
		this.m_HoareAnnotationFragments = hoareAnnotationFragments;
		this.m_UseEntry = true;
		m_PredicateTransformer = new PredicateTransformer(smtManager.getVariableManager(), 
				smtManager.getScript(), null, services);
	}

	public void addHoareAnnotationToCFG() {
		IPredicate precondForContext = m_SmtManager.getPredicateFactory().newPredicate(m_SmtManager.getScript().term("true"));
		addHoareAnnotationForContext(m_SmtManager, precondForContext,
				m_HoareAnnotationFragments.getProgPoint2StatesWithEmptyContext());

		for (IPredicate context : m_HoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().keySet()) {
			if (true || m_UseEntry || containsAnOldVar(context)) {
				precondForContext = m_HoareAnnotationFragments.getContext2Entry().get(context);
			} else {
				final Term spTerm = m_PredicateTransformer.strongestPostcondition(context,
						getCall((ISLPredicate) context), true);
				precondForContext = m_SmtManager.getPredicateFactory().newPredicate(spTerm);
			}
			precondForContext = m_SmtManager.renameGlobalsToOldGlobals(precondForContext);
			HashRelation<ProgramPoint, IPredicate> pp2preds = m_HoareAnnotationFragments
					.getDeadContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForContext(m_SmtManager, precondForContext, pp2preds);
		}

		for (IPredicate context : m_HoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().keySet()) {
			if (true || m_UseEntry || containsAnOldVar(context)) {
				precondForContext = m_HoareAnnotationFragments.getContext2Entry().get(context);
			} else {
				final Term spTerm = m_PredicateTransformer.strongestPostcondition(context,
						getCall((ISLPredicate) context), true);
				precondForContext = m_SmtManager.getPredicateFactory().newPredicate(spTerm);
			}
			precondForContext = m_SmtManager.renameGlobalsToOldGlobals(precondForContext);
			HashRelation<ProgramPoint, IPredicate> pp2preds = m_HoareAnnotationFragments
					.getLiveContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForContext(m_SmtManager, precondForContext, pp2preds);
		}
	}

	/**
	 * @param smtManager
	 * @param precondForContext
	 * @param pp2preds
	 */
	private void addHoareAnnotationForContext(SmtManager smtManager, IPredicate precondForContext,
			HashRelation<ProgramPoint, IPredicate> pp2preds) {
		for (ProgramPoint pp : pp2preds.getDomain()) {
			IPredicate[] preds = pp2preds.getImage(pp).toArray(new IPredicate[0]);
			Term tvp = smtManager.getPredicateFactory().or(false, preds);
			IPredicate formulaForPP = m_SmtManager.getPredicateFactory().newPredicate(tvp);
			addFormulasToLocNodes(pp, precondForContext, formulaForPP);
		}
	}

	private void addFormulasToLocNodes(ProgramPoint pp, IPredicate context, IPredicate current) {
		String procName = pp.getProcedure();
		String locName = pp.getPosition();
		ProgramPoint locNode = m_rootAnnot.getProgramPoints().get(procName).get(locName);
		HoareAnnotation hoareAnnot = null;
		
		HoareAnnotation taAnnot = HoareAnnotation.getAnnotation(locNode);
		if (taAnnot == null) {
			hoareAnnot = m_SmtManager.getPredicateFactory().getNewHoareAnnotation(pp, m_rootAnnot.getModGlobVarManager());
			hoareAnnot.annotate(locNode);
		} else {
			hoareAnnot = (HoareAnnotation) taAnnot;
		}
		hoareAnnot.addInvariant(context, current);
	}

	private Call getCall(ISLPredicate pred) {
		ProgramPoint pp = pred.getProgramPoint();
		Call result = null;
		for (RCFGEdge edge : pp.getOutgoingEdges()) {
			if (edge instanceof Call) {
				if (result == null) {
					result = (Call) edge;
				} else {
					throw new UnsupportedOperationException("several outgoing calls");
				}
			}
		}
		if (result == null) {
			throw new AssertionError("no outgoing call");
		}
		return result;
	}

	private boolean containsAnOldVar(IPredicate p) {
		for (BoogieVar bv : p.getVars()) {
			if (bv.isOldvar()) {
				return true;
			}
		}
		return false;
	}

}
