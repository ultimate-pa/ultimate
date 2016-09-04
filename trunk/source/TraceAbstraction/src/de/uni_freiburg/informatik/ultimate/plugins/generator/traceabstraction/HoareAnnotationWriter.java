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

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Write a Hoare annotation provided by HoareAnnotationFragments to the CFG.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationWriter {

	private final RootAnnot mrootAnnot;
	private final SmtManager mSmtManager;
	private final HoareAnnotationFragments mHoareAnnotationFragments;

	/**
	 * What is the precondition for a context? Strongest postcondition or entry
	 * given by automaton?
	 */
	private final boolean mUseEntry;
	private final PredicateTransformer mPredicateTransformer;

	public HoareAnnotationWriter(final RootAnnot rootAnnot, final SmtManager smtManager,
			final HoareAnnotationFragments hoareAnnotationFragments, final IUltimateServiceProvider services, 
			final SimplicationTechnique simplicationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mrootAnnot = rootAnnot;
		mSmtManager = smtManager;
		mHoareAnnotationFragments = hoareAnnotationFragments;
		mUseEntry = true;
		mPredicateTransformer = new PredicateTransformer(smtManager.getManagedScript(), 
				smtManager.getScript(), services, simplicationTechnique, xnfConversionTechnique);
	}

	public void addHoareAnnotationToCFG() {
		IPredicate precondForContext = mSmtManager.getPredicateFactory().newPredicate(mSmtManager.getScript().term("true"));
		addHoareAnnotationForContext(mSmtManager, precondForContext,
				mHoareAnnotationFragments.getProgPoint2StatesWithEmptyContext());

		for (final IPredicate context : mHoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().keySet()) {
			if (mUseEntry || containsAnOldVar(context)) {
				precondForContext = mHoareAnnotationFragments.getContext2Entry().get(context);
			} else {
				// compute SP
			}
			precondForContext = mSmtManager.renameGlobalsToOldGlobals(precondForContext);
			final HashRelation<ProgramPoint, IPredicate> pp2preds = mHoareAnnotationFragments
					.getDeadContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForContext(mSmtManager, precondForContext, pp2preds);
		}

		for (final IPredicate context : mHoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().keySet()) {
			if (mUseEntry || containsAnOldVar(context)) {
				precondForContext = mHoareAnnotationFragments.getContext2Entry().get(context);
			} else {
				// compute SP
			}
			precondForContext = mSmtManager.renameGlobalsToOldGlobals(precondForContext);
			final HashRelation<ProgramPoint, IPredicate> pp2preds = mHoareAnnotationFragments
					.getLiveContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForContext(mSmtManager, precondForContext, pp2preds);
		}
	}

	/**
	 * @param smtManager
	 * @param precondForContext
	 * @param pp2preds
	 */
	private void addHoareAnnotationForContext(final SmtManager smtManager, final IPredicate precondForContext,
			final HashRelation<ProgramPoint, IPredicate> pp2preds) {
		for (final ProgramPoint pp : pp2preds.getDomain()) {
			final IPredicate[] preds = pp2preds.getImage(pp).toArray(new IPredicate[0]);
			final Term tvp = smtManager.getPredicateFactory().or(false, preds);
			final IPredicate formulaForPP = mSmtManager.getPredicateFactory().newPredicate(tvp);
			addFormulasToLocNodes(pp, precondForContext, formulaForPP);
		}
	}

	private void addFormulasToLocNodes(final ProgramPoint pp, final IPredicate context, final IPredicate current) {
		final String procName = pp.getProcedure();
		final String locName = pp.getPosition();
		final ProgramPoint locNode = mrootAnnot.getProgramPoints().get(procName).get(locName);
		HoareAnnotation hoareAnnot = null;
		
		final HoareAnnotation taAnnot = HoareAnnotation.getAnnotation(locNode);
		if (taAnnot == null) {
			hoareAnnot = mSmtManager.getPredicateFactory().getNewHoareAnnotation(pp, mrootAnnot.getModGlobVarManager());
			hoareAnnot.annotate(locNode);
		} else {
			hoareAnnot = taAnnot;
		}
		hoareAnnot.addInvariant(context, current);
	}

	private Call getCall(final ISLPredicate pred) {
		final ProgramPoint pp = pred.getProgramPoint();
		Call result = null;
		for (final RCFGEdge edge : pp.getOutgoingEdges()) {
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

	private boolean containsAnOldVar(final IPredicate p) {
		for (final IProgramVar bv : p.getVars()) {
			if (bv.isOldvar()) {
				return true;
			}
		}
		return false;
	}

}
