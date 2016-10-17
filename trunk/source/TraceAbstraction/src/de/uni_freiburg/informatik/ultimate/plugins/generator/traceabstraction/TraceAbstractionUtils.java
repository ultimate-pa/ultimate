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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Provides static auxiliary methods for trace abstraction.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class TraceAbstractionUtils {

	
	
	
	public static <PRED extends IPredicate, PP> Collection<Set<IPredicate>> computePartition(
			final INestedWordAutomaton<CodeBlock, IPredicate> automaton, final ILogger logger, final Function<PRED, PP> ppProvider) {
		logger.debug("Start computation of initial partition.");
		final Collection<IPredicate> states = automaton.getStates();
		final HashRelation<PP, IPredicate> pp2p = new HashRelation<>();
		for (final IPredicate p : states) {
			final PRED sp = (PRED) p;
			pp2p.addPair(ppProvider.apply(sp), p);
		}
		final Collection<Set<IPredicate>> partition = new ArrayList<>();
		for (final PP pp : pp2p.getDomain()) {
			final Set<IPredicate> statesWithSamePP = new HashSet<>(pp2p.getImage(pp));
			partition.add(statesWithSamePP);
		}
		logger.debug("Finished computation of initial partition.");
		return partition;
	}
	

}
