package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DoubleDeckerVisitor;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SPredicate;


/**
 * Extract an interprocedural Hoare annotation from an abstraction. 
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class HoareAnnotationExtractor extends 
							DoubleDeckerVisitor<CodeBlock,IPredicate> {
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	Set<DoubleDecker<IPredicate>> m_ReportedDoubleDeckers = 
			new HashSet<DoubleDecker<IPredicate>>();
	
	private final HoareAnnotationFragments m_HoareAnnotation;
	
	public HoareAnnotationExtractor(
			INestedWordAutomatonOldApi<CodeBlock,IPredicate> abstraction, 
			HoareAnnotationFragments haf) {
		m_TraversedNwa = (INestedWordAutomatonOldApi<CodeBlock, IPredicate>) abstraction;
		m_HoareAnnotation = haf;		
		
		try {
			traverseDoubleDeckerGraph();
		} catch (OperationCanceledException e) {
			s_Logger.warn("Computation of Hoare annotation canceled.");
		}
	}


	private void addContext(DoubleDecker<IPredicate> doubleDecker) {
		if (!m_ReportedDoubleDeckers.contains(doubleDecker)) {
			IPredicate state = doubleDecker.getUp();
			IPredicate context = doubleDecker.getDown();
			m_HoareAnnotation.addDoubleDecker(context, state, m_TraversedNwa.getEmptyStackState());
			m_ReportedDoubleDeckers.add(doubleDecker);
		}
		
	}
	
	
	@Override
	protected Collection<IPredicate> getInitialStates() {
		Collection<IPredicate> result = m_TraversedNwa.getInitialStates();
		if (result.size() == 1) {
			//case where automaton is emtpy minimized and contains only one
			// dummy state.
			IPredicate p = result.iterator().next();
			if (!(p instanceof SPredicate)) {
				throw new AssertionError("No State Automaton would be ok");
				//result = new ArrayList<Predicate>(0);
			}
		}
		return result; 
	}
	
	@Override
	protected Collection<IPredicate> visitAndGetInternalSuccessors(
			DoubleDecker<IPredicate> doubleDecker) {
		addContext(doubleDecker);
		IPredicate state = doubleDecker.getUp();
		ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		for (CodeBlock symbol : m_TraversedNwa.lettersInternal(state)) {
			for (IPredicate succ : m_TraversedNwa.succInternal(state,symbol)) {
				succs.add(succ);
			}
		}
		return succs;
	}


	
	@Override
	protected Collection<IPredicate> visitAndGetCallSuccessors(
			DoubleDecker<IPredicate> doubleDecker) {
		addContext(doubleDecker);
		IPredicate state = doubleDecker.getUp();
		ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		Collection<CodeBlock> symbolsCall = m_TraversedNwa.lettersCall(state);
		if (symbolsCall.size() > 1) {
			throw new UnsupportedOperationException("Several outgoing calls not supported");
		}
		for (CodeBlock symbol : symbolsCall) {
			Iterable<IPredicate> succCall = m_TraversedNwa.succCall(state,symbol);
			Iterator<IPredicate> calls = succCall.iterator();
			calls.next();
			if (calls.hasNext()) {
				throw new UnsupportedOperationException("Several outgoing calls not supported");
			}
			for (IPredicate succ : succCall) {
				m_HoareAnnotation.addContextEntryPair(state, succ);
				succs.add(succ);
			}
		}
		return succs;
	}

	

	@Override
	protected Collection<IPredicate> visitAndGetReturnSuccessors(
			DoubleDecker<IPredicate> doubleDecker) {
		addContext(doubleDecker);
		IPredicate state = doubleDecker.getUp();
		IPredicate context = doubleDecker.getDown();
		ArrayList<IPredicate> succs = new ArrayList<IPredicate>();
		if (context == m_TraversedNwa.getEmptyStackState()) {
			return succs;
		}
		for (CodeBlock symbol : m_TraversedNwa.lettersReturn(state)) {
			for (IPredicate succ : m_TraversedNwa.succReturn(state,context,symbol)) {
				succs.add(succ);
			}
		}
		return succs;
	}
}
