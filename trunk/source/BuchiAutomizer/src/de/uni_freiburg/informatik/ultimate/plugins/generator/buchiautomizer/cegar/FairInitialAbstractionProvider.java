package de.uni_freiburg.informatik.ultimate.plugins.generator.buchiautomizer.cegar;

import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.initialabstraction.IInitialAbstractionProvider;

public class FairInitialAbstractionProvider<L extends IIcfgTransition<?>> implements IInitialAbstractionProvider<L,
INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> {
	private IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> mInitialAbstractionProvider;
	private IIcfg<?> mIcfg;
	
	public FairInitialAbstractionProvider(IIcfg<?> icfg, IInitialAbstractionProvider<L, ? extends INwaOutgoingLetterAndTransitionProvider<L, IPredicate>> initialAbstractionProvider) {
		mInitialAbstractionProvider = initialAbstractionProvider;
		mIcfg = icfg;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getInitialAbstraction(
			IIcfg<? extends IcfgLocation> icfg, Set<? extends IcfgLocation> errorLocs) throws AutomataLibraryException {
		for (Entry<String, ? extends IcfgLocation> procedureEntry : icfg.getProcedureEntryNodes().entrySet()) {
			getFairAutomaton(procedureEntry.getValue());
		}
		return mInitialAbstractionProvider.getInitialAbstraction(icfg, errorLocs);
	}
	
	private NestedWordAutomaton<L, IPredicate> getFairAutomaton(IcfgLocation entryLocation) {
		//NestedWordAutomaton<L, IPredicate> fairAutomaton = new NestedWordAutomaton<>(services, vpAlphabet, emptyStateFactory);
		return null;
		
	}

}
