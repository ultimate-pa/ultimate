/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.ProcedureResources.OverlaySuccessors;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing.UniqueMarkTransition;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgSummaryTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;

/**
 * Annotates given program locations with predicates over-approximating the actually reachable concrete states at that
 * locations.
 *
 * @see #interpret()
 *
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class SymbolicInterpreter {

	private final IIcfg<IcfgLocation> mIcfg;
	private final CallGraph mCallGraph;
	private Map<String, ProcedureResources> mProcResources = new HashMap<>();
	private final WorklistWithInputs<String> mEnterCallWorklist;
	private final Map<IcfgLocation, IPredicate> mPredicatesForLOI = new HashMap<>();
	private final PredicateUtils mPredicateUtils;
	
	/**
	 * Creates a new interpreter assuming all error locations to be locations of interest.
	 * @see #interpret()
	 */
	public SymbolicInterpreter(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg) {
		this(services, icfg, icfg.getProcedureErrorNodes().values().stream()
				.flatMap(Set::stream).collect(Collectors.toList()));
	}

	/**
	 * Creates a new interpret using a custom set of locations of interest.
	 * @param locationsOfInterest Locations for which predicates shall be computed.
	 * @see #interpret()
	 */
	public SymbolicInterpreter(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest) {
		mIcfg = icfg;
		mPredicateUtils = new PredicateUtils(services, mIcfg);
		mEnterCallWorklist = new WorklistWithInputs<>(mPredicateUtils::merge);
		mCallGraph = new CallGraph(icfg, locationsOfInterest);
		initPredicates(locationsOfInterest);
		enqueInitial();
	}

	private void enqueInitial() {
		final IPredicate top = mPredicateUtils.top();
		mCallGraph.initialProceduresOfInterest().stream()
			.peek(proc -> mEnterCallWorklist.add(proc, top))
			.map(mIcfg.getProcedureEntryNodes()::get)
			.forEach(procEntry -> storePredicateIfLOI(procEntry, top));
	}

	private void initPredicates(final Collection<IcfgLocation> locationsOfInterest) {
		final IPredicate bottom = mPredicateUtils.bottom();
		locationsOfInterest.forEach(loi -> mPredicatesForLOI.put(loi, bottom));
	}

	/**
	 * Interprets the ICFG starting at the initial nodes.
	 * 
	 * @return Map from all locations of interest given in
	 *         {@link #SymbolicInterpreter(IUltimateServiceProvider, IIcfg, Collection)}
	 *          to predicates over-approximating the program states at these locations
	 */
	public Map<IcfgLocation, IPredicate> interpret() {
		while (mEnterCallWorklist.advance()) {
			final String procedure = mEnterCallWorklist.getWork();
			final IPredicate input = mEnterCallWorklist.getInput();
			final ProcedureResources resources = mProcResources.computeIfAbsent(procedure, this::computeProcResources);
			interpretLOIsInProcedure(resources, input);
		}
		return mPredicatesForLOI;
	}

	private void interpretLOIsInProcedure(final ProcedureResources resources, final IPredicate initalInput) {
		final OverlaySuccessors overlaySuccessors = resources.getDagOverlayPathToLOIsAndEnterCalls();
		final WorklistWithInputs<RegexDagNode<IIcfgTransition<IcfgLocation>>> worklist =
				new WorklistWithInputs<>(mPredicateUtils::merge);
		worklist.add(resources.getRegexDag().getSource(), initalInput);
		while (worklist.advance()) {
			final RegexDagNode<IIcfgTransition<IcfgLocation>> currentNode = worklist.getWork();
			final IPredicate currentInput = worklist.getInput();
			final IPredicate currentOutput = interpretNode(currentNode, currentInput);
			overlaySuccessors.getImage(currentNode).forEach(successor -> worklist.add(successor, currentOutput));
		}
	}

	private ProcedureResources computeProcResources(final String procedure) {
		return new ProcedureResources(mIcfg, procedure, mCallGraph.locationsOfInterest(procedure),
				mCallGraph.successorsOfInterest(procedure));
	}

	private IPredicate interpretNode(final RegexDagNode<IIcfgTransition<IcfgLocation>> node, final IPredicate input) {
		final IRegex<IIcfgTransition<IcfgLocation>> regex = node.getContent();
		if (regex instanceof Literal) {
			return interpretTransition(((Literal<IIcfgTransition<IcfgLocation>>) regex).getLetter(), input);
		} else if (regex instanceof Epsilon) {
			// Nothing to do. Multiple inputs for the same node are merged inside the worklist.
			// Merging always applies because we traverse DAG using BFS.
			return input;
		} else if (regex instanceof Star) {
			throw new UnsupportedOperationException("Loop handling not implemented yet: " + regex);
		} else {
			throw new UnsupportedOperationException("Unexpected node type in dag: " + regex.getClass());
		}
	}

	private IPredicate interpretTransition(final IIcfgTransition<IcfgLocation> transition, final IPredicate input) {
		if (transition instanceof UniqueMarkTransition) {
			// TODO Do we have to do more? Does this cause more work than needed?
			// TODO Maybe we don't need UniqueMarkTransition at all.
			return input;
		} else if (transition instanceof IIcfgSummaryTransition<?>) {
			throw new UnsupportedOperationException("Call summaries not implemented yet: " + transition);
		} else if (transition instanceof IIcfgCallTransition<?>) {
			return interpretEnterCall((IIcfgCallTransition<IcfgLocation>) transition, input);
		} else if (transition instanceof IIcfgInternalTransition) {
			return interpretInternal((IIcfgInternalTransition<IcfgLocation>) transition, input);
		} else {
			throw new UnsupportedOperationException("Unexpected transition type: " + transition.getClass());
		}
	}

	private IPredicate interpretInternal(final IIcfgInternalTransition<IcfgLocation> transition,
			final IPredicate input) {
		final IPredicate output = mPredicateUtils.post(input, transition);
		storePredicateIfLOI(transition.getTarget(), output);
		return output;
	}

	private IPredicate interpretEnterCall(final IIcfgCallTransition<IcfgLocation> transition, final IPredicate input) {
		IPredicate calleeInput = mPredicateUtils.postCall(input, transition);
		mEnterCallWorklist.add(transition.getSucceedingProcedure(), calleeInput);
		storePredicateIfLOI(transition.getTarget(), calleeInput);
		return calleeInput;
	}

	private void storePredicateIfLOI(final IcfgLocation location, final IPredicate addPredicate) {
		mPredicatesForLOI.computeIfPresent(location,
				(unused, oldPredicate) -> mPredicateUtils.merge(oldPredicate, addPredicate));
	}


}
