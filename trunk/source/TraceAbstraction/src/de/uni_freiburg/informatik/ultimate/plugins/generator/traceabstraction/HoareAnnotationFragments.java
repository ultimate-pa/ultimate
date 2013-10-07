package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval.UpDownEntry;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.model.IAnnotations;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager.TermVarsProc;

/**
 * Store and maintain fragments of a Hoare Annotation derived during abstraction
 * refinement. This is only necessary if we minimize the abstraction during
 * refinement by removing states from which can not reach any accepting state.
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * 
 */
public class HoareAnnotationFragments {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);

	protected Map<ProgramPoint, Map<IPredicate, Collection<IPredicate>>> m_ProgPoint2Context2State = 
			new HashMap<ProgramPoint, Map<IPredicate, Collection<IPredicate>>>();
	protected Map<IPredicate, IPredicate> m_Context2Entry = 
			new HashMap<IPredicate, IPredicate>();
	protected Map<ProgramPoint, Collection<IPredicate>> m_ProgPoint2StatesWithEmptyContext = 
			new HashMap<ProgramPoint, Collection<IPredicate>>();
	protected Map<IPredicate, Collection<ProgramPoint>> m_Context2ProgPoint = 
			new HashMap<IPredicate, Collection<ProgramPoint>>();
	private final Set<IPredicate> m_ReplacedContexts = 
			new HashSet<IPredicate>();
	
	private final RootAnnot m_rootAnnot;
	private final SmtManager m_SmtManager;
	
	/**
	 * What is the precondition for a context?
	 * Strongest postcondition or entry given by automaton?
	 */
	private final boolean m_UseEntry;

	
	
	
	public HoareAnnotationFragments(RootAnnot rootAnnot, SmtManager smtManager, boolean useEntry) {
		this.m_rootAnnot = rootAnnot;
		this.m_SmtManager = smtManager;
		this.m_UseEntry = useEntry;
	}

	/**
	 * Announce that during abstraction refinement state psOld of the old
	 * abstraction was replaced by psNew of the new abstraction. All Invariants
	 * which were assigned to psOld will be assigned to psNew. The entry of
	 * psNew is set to null to indicate that we don't know the entry yet. psOld
	 * is added to the set of replaced contexts. Should be called while doing an
	 * abstraction refinement.
	 */
	public void announceReplacement(IPredicate psOld, IPredicate psNew) {
		if (!m_Context2ProgPoint.containsKey(psOld)) {
			return;
		}
		Collection<ProgramPoint> programPoints = m_Context2ProgPoint.get(psOld);
		for (ProgramPoint pp : programPoints) {
			Map<IPredicate, Collection<IPredicate>> context2states = 
					m_ProgPoint2Context2State.get(pp);
			Collection<IPredicate> oldStates = context2states.get(psOld);
			assert (oldStates != null);
			assert (!oldStates.isEmpty());
			Collection<IPredicate> newStates = new ArrayList<IPredicate>();
			newStates.addAll(oldStates);
			context2states.put(psNew, newStates);
			Collection<ProgramPoint> progpoints = m_Context2ProgPoint.get(psNew);
			if (progpoints == null) {
				progpoints = new HashSet<ProgramPoint>();
				m_Context2ProgPoint.put(psNew, progpoints);
			}
			progpoints.add(pp);
			m_ReplacedContexts.add(psOld);

			IPredicate oldEntry = m_Context2Entry.get(psOld);
			// use the oldEntry. Necessary in cases where the entry has already
			// been removed. If the oldEntry is still there (and was replaced by
			// a different state the entry of psNew will be updated when this
			// entry is removed.
			m_Context2Entry.put(psNew, oldEntry);

		}
	}

	/**
	 * Remove all contexts that have been marked as replaced. Should be called
	 * after a refinement step.
	 */
	public void wipeReplacedContexts() {
		for (IPredicate context : m_ReplacedContexts) {
			assert !m_Context2ProgPoint.get(context).isEmpty();
			Collection<ProgramPoint> programPoints = m_Context2ProgPoint.get(context);
			for (ProgramPoint pp : programPoints) {
				Map<IPredicate, Collection<IPredicate>> context2states = 
						m_ProgPoint2Context2State.get(pp);
				Collection<IPredicate> removedContext = context2states.remove(context);
				assert (removedContext != null);
			}
			m_Context2Entry.remove(context);
			m_Context2ProgPoint.remove(context);
		}
		m_ReplacedContexts.clear();
	}

	public void addDoubleDecker(IPredicate down, IPredicate up,IPredicate emtpy) {
		ProgramPoint pp = ((SPredicate) up).getProgramPoint();
		if (down == emtpy) {
			Collection<IPredicate> statesWithEmtpyContext = m_ProgPoint2StatesWithEmptyContext.get(pp);
			if (statesWithEmtpyContext == null) {
				statesWithEmtpyContext = new ArrayList<IPredicate>();
				m_ProgPoint2StatesWithEmptyContext.put(pp,statesWithEmtpyContext);
			}
			statesWithEmtpyContext.add(up);
		} else {
			Map<IPredicate, Collection<IPredicate>> context2states = m_ProgPoint2Context2State.get(pp);
			if (context2states == null) {
				context2states = new HashMap<IPredicate, Collection<IPredicate>>();
				m_ProgPoint2Context2State.put(pp, context2states);
			}
			Collection<IPredicate> states = context2states.get(down);
			if (states == null) {
				states = new ArrayList<IPredicate>();
				context2states.put(down, states);
			}
			states.add(up);

			Collection<ProgramPoint> programPoints = m_Context2ProgPoint.get(down);
			if (programPoints == null) {
				programPoints = new HashSet<ProgramPoint>();
				m_Context2ProgPoint.put(down, programPoints);
			}
			programPoints.add(pp);
		}
	}
	
	
	/**
	 * Replace all contexts in the preimage of oldState2newState by the
	 * image of oldState2newState. 
	 * The mapping oldState2newState might "merge
	 * states" (map several to one). In this case the states/ProgramPoints of 
	 * the new context are the union of the states/ProgramPoints of the old
	 * contexts.
	 * 
	 */
	public void updateContexts(Map<IPredicate, IPredicate> oldState2newState) {
		assert (m_ReplacedContexts.isEmpty()) : "seems there is already an update going on";
		for (IPredicate pOld : oldState2newState.keySet()) {
			if (m_Context2ProgPoint.containsKey(pOld)) {
				IPredicate pNew = oldState2newState.get(pOld);
				updateContext(pOld, pNew);
			}
		}
	}

	/**
	 * Replace the context oldContext by newContext.
	 * If newContext already exists, add the states/ProgramPoints of the old 
	 * context to the states/ProgramPoints the new context.
	 */
	private void updateContext(IPredicate oldContext, IPredicate newContext) {
		Collection<ProgramPoint> ppsOfContext = m_Context2ProgPoint.get(oldContext);
		for (ProgramPoint pp : ppsOfContext) {
			assert(m_ProgPoint2Context2State.containsKey(pp));
			Map<IPredicate, Collection<IPredicate>> context2State = 
					m_ProgPoint2Context2State.get(pp);
			Collection<IPredicate> statesOfNewContext = context2State.get(newContext);
			if (statesOfNewContext == null) {
				statesOfNewContext = new HashSet<IPredicate>();
				context2State.put(newContext, statesOfNewContext);
			}
			assert(context2State.containsKey(oldContext));
			Collection<IPredicate> statesOfOldContext = context2State.get(oldContext);
			statesOfNewContext.addAll(statesOfOldContext);
			context2State.remove(oldContext);
		}
		m_Context2ProgPoint.remove(oldContext);
		m_Context2ProgPoint.put(newContext, ppsOfContext);
		
		// as mentioned in some comment above
		// use the oldEntry. Necessary in cases where the entry has already
		// been removed. If the oldEntry is still there (and was replaced by
		// a different state the entry of psNew will be updated when this
		// entry is removed.
		assert (m_Context2Entry.containsKey(oldContext));
		IPredicate entryOfContext = m_Context2Entry.get(oldContext);
		m_Context2Entry.remove(oldContext);
		m_Context2Entry.put(newContext, entryOfContext);
	}
	
	
	
	

//	public static Predicate computeProcedureEntryForCaller(
//			Predicate down,
//			NestedWordAutomaton<TransAnnot, Predicate> nwa) {
//		Collection<TransAnnot> calls = nwa.symbolsCall(down);
//		if (calls.size() < 1) {
//			throw new AssertionError(
//					"each down state should have outgoing call");
//		}
//		Collection<Predicate> callSuccs = new ArrayList<Predicate>();
//		for (TransAnnot call : calls) {
//			callSuccs.addAll(nwa.succCall(down, call));
//		}
//		if (callSuccs.size() != 1) {
//			throw new AssertionError(
//					"unable to determine successor, I have problems if location has several outgoing calls");
//		}
//		return callSuccs.iterator().next();
//	}
	
	public void addContextEntryPair(IPredicate context, IPredicate entry) {
//		Predicate oldEntry = m_Context2Entry.get(context);
//		assert( oldEntry == null || oldEntry == entry);
		m_Context2Entry.put(context, entry);
	}
	
	

//	public void addDoubleDeckers(
//			Map<Predicate, Set<Predicate>> removedDoubleDeckers,
//			Predicate emptyStack) {
//		for (Predicate up : removedDoubleDeckers.keySet()) {
//			for (Predicate down : removedDoubleDeckers.get(up)) {
//				addDoubleDecker(down, up, emptyStack);
//			}
//		}
//
//	}
//
//	public void addContext2Entry(Map<Predicate, Predicate> context2entry) {
//		m_Context2Entry.putAll(context2entry);
//	}
	
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
		
//		RCfgState rcfgstate = locNode.getStateAnnot();
//		rcfgstate.addInvariant(context, current);
	}

	
	public void addHoareAnnotationToCFG(SmtManager smtManager) {
		
		for (ProgramPoint pp : m_ProgPoint2StatesWithEmptyContext.keySet()) {
			IPredicate formulaForEmptyContext = m_SmtManager.newFalsePredicate();
			Collection<IPredicate> statesWithEmptyContxt = 
					m_ProgPoint2StatesWithEmptyContext.get(pp);
			for (IPredicate state : statesWithEmptyContxt) {
				TermVarsProc tvp = smtManager.or(formulaForEmptyContext, state);
				formulaForEmptyContext = m_SmtManager.newPredicate(tvp.getFormula(), 
						tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
			}
			IPredicate precondForContext = m_SmtManager.newTruePredicate();
			addFormulasToLocNodes(pp, precondForContext, formulaForEmptyContext);
		}	

		for (ProgramPoint pp : m_ProgPoint2Context2State.keySet()) {
			Map<IPredicate, Collection<IPredicate>> context2states = 
					m_ProgPoint2Context2State.get(pp);
			for (IPredicate context : context2states.keySet()) {
				IPredicate formulaForContext = m_SmtManager.newFalsePredicate();
				Collection<IPredicate> states = context2states.get(context);
				for (IPredicate state : states) {
					TermVarsProc tvp = smtManager.or(formulaForContext, state);
					formulaForContext = m_SmtManager.newPredicate(tvp.getFormula(), 
							tvp.getProcedures(), tvp.getVars(), tvp.getClosedFormula());
				}
				IPredicate precondForContext;
					if (true || m_UseEntry || containsAnOldVar(context)) {
						precondForContext = m_Context2Entry.get(context);
					} else {
						precondForContext = smtManager.strongestPostcondition(context, getCall((ISLPredicate) context), true);
					}
				precondForContext = smtManager.renameGlobalsToOldGlobals(precondForContext);
				addFormulasToLocNodes(pp, precondForContext, formulaForContext);
			}
		}
	}

	public void addDeadEndDoubleDeckers(
			IOpWithDelayedDeadEndRemoval<CodeBlock, IPredicate> diff) throws OperationCanceledException {
		IPredicate emtpyStack = diff.getResult().getEmptyStackState();
		for (UpDownEntry<IPredicate> upDownEntry : diff.getRemovedUpDownEntry()) {
			addDoubleDecker(upDownEntry.getDown(), upDownEntry.getUp(), emtpyStack);
			if (upDownEntry.getEntry() != null) {
				addContextEntryPair(upDownEntry.getDown(), upDownEntry.getEntry());
			} else {
				assert upDownEntry.getDown() == emtpyStack;
			}

		}
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
