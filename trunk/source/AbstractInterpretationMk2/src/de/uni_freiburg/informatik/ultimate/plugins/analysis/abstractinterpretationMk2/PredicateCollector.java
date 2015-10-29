package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationMk2.abstractdomain.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootAnnot;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public final class PredicateCollector {

	private final IUltimateServiceProvider mServices;
	private final Logger mLogger;

	public PredicateCollector(final IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(AIActivator.PLUGIN_ID);
		
		//Map<RCFGNode, List<StackState>> abstractStates
	}

	private void collect(final Function<RCFGNode, List<StackState<?>>> abstractStateProvider, final RootNode root) {
		final RootAnnot rootAnnot = root.getRootAnnot();
		final Boogie2SMT bpl2smt = rootAnnot.getBoogie2SMT();
		final ModifiableGlobalVariableManager mgvMan = rootAnnot.getModGlobVarManager();

		// TODO: use predicate unifier
		// SmtManager smtMan = new SmtManager(tcSolver, bpl2smt,
		// mgvMan, mServices);
		// PredicateUnifier predUnifier = new PredicateUnifier(mServices,
		// smtMan);

		// TODO: Save predicate in useful way, i.e., as annotation of
		// programpoint

		final Set<RCFGNode> processed = new HashSet<>();
		final Deque<RCFGNode> worklist = new ArrayDeque<>();
		worklist.add(root);

		while (!worklist.isEmpty()) {
			final RCFGNode current = worklist.remove();
			if (!processed.add(current)) {
				continue;
			}
			worklist.addAll(current.getOutgoingNodes());
			
			final List<StackState<?>> absStackStates = abstractStateProvider.apply(current);
			for(final StackState<?> absStackState : absStackStates){
				IAbstractState<?> currentAbsState = absStackState.getCurrentState();
			}

		}
	}

}
