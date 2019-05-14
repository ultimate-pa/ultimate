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

import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Epsilon;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.IRegex;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Literal;
import de.uni_freiburg.informatik.ultimate.lib.pathexpressions.regex.Star;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.ProcedureResources.OverlaySuccessors;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.cfgpreprocessing.CallReturnSummary;
import de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation.regexdag.RegexDagNode;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Annotates given program locations with predicates over-approximating the actually reachable concrete states at that
 * locations.
 *
 * @author Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 */
public class SymbolicInterpreter {

	private final IIcfg<IcfgLocation> mIcfg;
	private final CallGraph mCallGraph;
	private Map<String, ProcedureResources> mProcResources = new HashMap<>();
	private final WorklistWithInputs<String> mEnterCallWorklist = new WorklistWithInputs<>();
	private final Map<IcfgLocation, SymbolicState> mPredicatesForLOI = new HashMap<>();

	public SymbolicInterpreter(final IIcfg<IcfgLocation> icfg) {
		this(icfg, icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toList()));
	}

	public SymbolicInterpreter(final IIcfg<IcfgLocation> icfg, final Collection<IcfgLocation> locationsOfInterest) {
		mIcfg = icfg;
		mCallGraph = new CallGraph(icfg, locationsOfInterest);
		initPredicates(locationsOfInterest);
		enqueInitial();
	}

	private void enqueInitial() {
		mCallGraph.initialProceduresOfInterest().forEach(proc -> mEnterCallWorklist.add(proc, new SymbolicState()));
	}

	private void initPredicates(final Collection<IcfgLocation> locationsOfInterest) {
		// TODO create bottom symbol instead of this dummy
		final SymbolicState bottom = new SymbolicState();
		locationsOfInterest.forEach(loi -> mPredicatesForLOI.put(loi, bottom));
	}

	public void interpret() {
		while (mEnterCallWorklist.advance()) {
			final String procedure = mEnterCallWorklist.getWork();
			final SymbolicState input = mEnterCallWorklist.getInput();
			final ProcedureResources resources = mProcResources.computeIfAbsent(procedure, this::computeProcResources);
			interpretLOIsInProcedure(resources, input);
		}
	}

	private void interpretLOIsInProcedure(final ProcedureResources resources, final SymbolicState initalInput) {
		final OverlaySuccessors overlaySuccessors = resources.getDagOverlayPathToLOIsAndEnterCalls();
		final WorklistWithInputs<RegexDagNode<IIcfgTransition<IcfgLocation>>> worklist = new WorklistWithInputs<>();
		worklist.add(resources.getRegexDag().getSource(), initalInput);
		while (worklist.advance()) {
			final RegexDagNode<IIcfgTransition<IcfgLocation>> currentNode = worklist.getWork();
			final SymbolicState currentInput = worklist.getInput();
			final SymbolicState currentOutput = interpretNode(currentNode, currentInput);
			overlaySuccessors.getImage(currentNode).forEach(successor -> worklist.add(successor, currentOutput));
		}
	}

	private ProcedureResources computeProcResources(final String procedure) {
		return new ProcedureResources(mIcfg, procedure, mCallGraph.locationsOfInterest(procedure),
				mCallGraph.successorsOfInterest(procedure));
	}

	private SymbolicState interpretNode(final RegexDagNode<IIcfgTransition<IcfgLocation>> node,
			final SymbolicState input) {
		final IRegex<IIcfgTransition<IcfgLocation>> regex = node.getContent();
		if (regex instanceof Literal) {
			return interpretLiteral(((Literal<IIcfgTransition<IcfgLocation>>) regex).getLetter(), input);
		} else if (regex instanceof Epsilon) {
			// Nothing to do. Multiple inputs for the same node are merged inside the worklist.
			// Merging is applied because we traverse DAG using BFS.
			return input;
		} else if (regex instanceof Star) {
			throw new UnsupportedOperationException("Loop handling not implemented yet: " + regex);
		} else {
			throw new UnsupportedOperationException("Unexpected node type in dag: " + regex);
		}
	}

	// TODO compute using post
	private SymbolicState interpretLiteral(final IIcfgTransition<IcfgLocation> letter, final SymbolicState input) {
		if (letter instanceof CallReturnSummary) {
			throw new UnsupportedOperationException("Call summaries not implemented yet: " + letter);
		} else if (letter instanceof IcfgCallTransition) {
			// TODO process transformula to compute input for function
			throw new UnsupportedOperationException("Enter calls not implemented yet: " + letter);
			// mEnterCallWorklist.add(letter.getSucceedingProcedure(), computedInput);
		} else if (letter instanceof IIcfgInternalTransition) {
			return interpretInternal((IIcfgInternalTransition<IcfgLocation>) letter, input);
		} else {
			throw new UnsupportedOperationException("Unexpected transition type: " + letter);
		}
	}

	private SymbolicState interpretInternal(final IIcfgInternalTransition<IcfgLocation> transition,
				final SymbolicState input) {
		// TODO apply post to compute output
		final SymbolicState output = new SymbolicState();
		// TODO only target? what if source location is also a LOI? call storePred somewhere else too?
		storePredicateIfLOI(transition.getTarget(), output);
		return output;
	}

	private void storePredicateIfLOI(final IcfgLocation location, final SymbolicState addPredicate) {
		mPredicatesForLOI.computeIfPresent(location, (unused, oldPredicate) -> oldPredicate.merge(addPredicate));
	}


}
