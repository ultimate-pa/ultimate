package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;

public class FairInitialAbstractionProvider<L extends IIcfgTransition<?>> implements IInitialAbstractionProvider<L,
INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {
	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mInitialAbstractionProvider;
	private IIcfg<?> mIcfg;
	private AutomataLibraryServices mServices;
	private PredicateFactoryRefinement mStateFactory;
	private IcfgEdgeIterator mIcfgEdgeIterator;
	private Set<IcfgEdge> mIcfgAlphabet;
	private Map<String, Set<IcfgEdge>> mProcedureAlphabetMap;
	private Map<String, NestedWordAutomaton<L, IPredicate>> mFairAutomataList;
	
	public FairInitialAbstractionProvider(IIcfg<?> icfg, IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>>
	initialAbstractionProvider, AutomataLibraryServices services, PredicateFactoryRefinement stateFactoryForRefinement) {
		mInitialAbstractionProvider = initialAbstractionProvider;
		mIcfg = icfg;
		mServices = services;
		mStateFactory = stateFactoryForRefinement;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getInitialAbstraction(
			IIcfg<? extends IcfgLocation> icfg, Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction = mInitialAbstractionProvider.getInitialAbstraction(icfg, errorLocs);
		IEmptyStackStateFactory<IPredicate> stateFactory = new IEmptyStackStateFactory<IPredicate>() {
			@Override
			public IPredicate createEmptyStackState() {
				// TODO Auto-generated method stub
				return null;
			}
		};
		mIcfgEdgeIterator = new IcfgEdgeIterator(mIcfg);
		//compute the alphabet of each procedure
		while(mIcfgEdgeIterator.hasNext()) {
			IcfgEdge edge = mIcfgEdgeIterator.next();
			mIcfgAlphabet.add(edge);
			String procedure = edge.getPrecedingProcedure();
			Set<IcfgEdge> procedureAlphabet = Collections.emptySet();
			if (mProcedureAlphabetMap.containsKey(procedure)) {
				procedureAlphabet = mProcedureAlphabetMap.get(procedure);
			}
			procedureAlphabet.add(edge.getLabel());
			mProcedureAlphabetMap.put(procedure, procedureAlphabet);
		}
		//compute the fair automaton of each procedure
		for (Entry<String, ? extends IcfgLocation> procedureEntry : icfg.getProcedureEntryNodes().entrySet()) {
			mFairAutomataList.put(procedureEntry.getKey(), getFairAutomaton(initialAbstraction, stateFactory, procedureEntry.getValue()));
		}
		
		return mInitialAbstractionProvider.getInitialAbstraction(icfg, errorLocs);
	}
	
	private NestedWordAutomaton<L, IPredicate> getFairAutomaton(INwaOutgoingLetterAndTransitionProvider<L, IPredicate> initialAbstraction,
			IEmptyStackStateFactory<IPredicate> stateFactory, IcfgLocation entryLocation) {
		VpAlphabet<L> alphabet = initialAbstraction.getVpAlphabet();
		NestedWordAutomaton<L, IPredicate> fairAutomaton = new NestedWordAutomaton<L, IPredicate>(mServices, alphabet, stateFactory);

		IPredicate s1 = stateFactory.createEmptyStackState();
		IPredicate s2 = stateFactory.createEmptyStackState();
		IPredicate s3 = stateFactory.createEmptyStackState();
		fairAutomaton.addState(true, true, s1);
		fairAutomaton.addState(false, false, s2);
		fairAutomaton.addState(false, true, s3);
		String procedure = entryLocation.getProcedure();
		Set<IcfgEdge> procedureAlphabet = mProcedureAlphabetMap.get(procedure);
		
		//construct outgoing edges of s1
		List<IcfgEdge> entryEdges = entryLocation.getIncomingEdges();
		for (IcfgEdge edge : mIcfgAlphabet ) {
			if(!entryEdges.contains(edge)) {
				fairAutomaton.addInternalTransition(s1, (L) edge, s1);
			} else {
				fairAutomaton.addInternalTransition(s1, (L) edge, s2);
			}
		}
		
		IcfgLocation exit = mIcfg.getProcedureExitNodes().get(procedure);
		List<IcfgEdge> exitEdges = exit.getOutgoingEdges();
		
		//construct outgoing edges of s2 and s3
		for(IcfgEdge edge : mIcfgAlphabet) {
			if(procedureAlphabet.contains(edge)) {
				fairAutomaton.addInternalTransition(s2, (L) edge, s3);
				fairAutomaton.addInternalTransition(s3, (L) edge, s3);
			} else if (exitEdges.contains(edge)) {
				fairAutomaton.addInternalTransition(s2, (L) edge, s1);
				fairAutomaton.addInternalTransition(s3, (L) edge, s1);
			} else {
				fairAutomaton.addInternalTransition(s2, (L) edge, s2);
				fairAutomaton.addInternalTransition(s3, (L) edge, s2);
				
			}
		}		
		return fairAutomaton;
	}

}
