package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.annotation.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;

/**
 * Write a Hoare annotation provided by HoareAnnotationFragments to the CFG.   
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationWriter {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

	private final RootAnnot m_rootAnnot;
	private final SmtManager m_SmtManager;
	private final HoareAnnotationFragments m_HoareAnnotationFragments;
	
	/**
	 * What is the precondition for a context?
	 * Strongest postcondition or entry given by automaton?
	 */
	private final boolean m_UseEntry;
	private final PredicateTransformer m_PredicateTransformer; 
	
	
	
	public HoareAnnotationWriter(RootAnnot rootAnnot, SmtManager smtManager, 
			HoareAnnotationFragments hoareAnnotationFragments) {
		this.m_rootAnnot = rootAnnot;
		this.m_SmtManager = smtManager;
		this.m_HoareAnnotationFragments = hoareAnnotationFragments;
		this.m_UseEntry = true;
		m_PredicateTransformer = new PredicateTransformer(smtManager, null);
	}


	public void addHoareAnnotationToCFG() {
		IPredicate precondForContext = m_SmtManager.newTruePredicate();
		addHoareAnnotationForContext(m_SmtManager, precondForContext, m_HoareAnnotationFragments.getProgPoint2StatesWithEmptyContext());
		
		for (IPredicate context : m_HoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().keySet()) {
			if (true || m_UseEntry || containsAnOldVar(context)) {
				precondForContext = m_HoareAnnotationFragments.getContext2Entry().get(context);
			} else {
				precondForContext = m_PredicateTransformer.strongestPostcondition(context, getCall((ISLPredicate) context), true);
			}
			precondForContext = m_SmtManager.renameGlobalsToOldGlobals(precondForContext);
			HashRelation<ProgramPoint, IPredicate> pp2preds = m_HoareAnnotationFragments.getDeadContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForContext(m_SmtManager, precondForContext,
					pp2preds);
		}
		
		for (IPredicate context : m_HoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().keySet()) {
			if (true || m_UseEntry || containsAnOldVar(context)) {
				precondForContext = m_HoareAnnotationFragments.getContext2Entry().get(context);
			} else {
				precondForContext = m_PredicateTransformer.strongestPostcondition(context, getCall((ISLPredicate) context), true);
			}
			precondForContext = m_SmtManager.renameGlobalsToOldGlobals(precondForContext);
			HashRelation<ProgramPoint, IPredicate> pp2preds = m_HoareAnnotationFragments.getLiveContexts2ProgPoint2Preds().get(context);
			addHoareAnnotationForContext(m_SmtManager, precondForContext,
					pp2preds);
		}
	}
	
	
	/**
	 * @param smtManager
	 * @param precondForContext
	 * @param pp2preds
	 */
	private void addHoareAnnotationForContext(SmtManager smtManager,
			IPredicate precondForContext,
			HashRelation<ProgramPoint, IPredicate> pp2preds) {
		for (ProgramPoint pp : pp2preds.getDomain()) {
			IPredicate[] preds = pp2preds.getImage(pp).toArray(new IPredicate[0]);
			TermVarsProc tvp = smtManager.or(preds);
			IPredicate formulaForPP = m_SmtManager.newPredicate(tvp.getFormula(), 
					tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
			addFormulasToLocNodes(pp, precondForContext, formulaForPP);
		}
	}
	
	private void addFormulasToLocNodes(ProgramPoint pp, IPredicate context, 
			IPredicate current) {
		String procName = pp.getProcedure();
		String locName = pp.getPosition();
		ProgramPoint locNode = m_rootAnnot.getProgramPoints().get(procName).get(locName);
		HoareAnnotation hoareAnnot = null;
		IAnnotations taAnnot = locNode.getPayload().getAnnotations().get(Activator.s_PLUGIN_ID);
		if (taAnnot == null) {
			hoareAnnot = m_SmtManager.getNewHoareAnnotation(pp); 
			locNode.getPayload().getAnnotations().put(Activator.s_PLUGIN_ID, hoareAnnot);
		} else {
			hoareAnnot = (HoareAnnotation) taAnnot;
		}
		hoareAnnot.addInvariant(context, current);
	}
	
	
	private Call getCall(ISLPredicate pred) {
		ProgramPoint pp = pred.getProgramPoint();
		Call result = null;
		for (RCFGEdge edge  : pp.getOutgoingEdges()) {
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
