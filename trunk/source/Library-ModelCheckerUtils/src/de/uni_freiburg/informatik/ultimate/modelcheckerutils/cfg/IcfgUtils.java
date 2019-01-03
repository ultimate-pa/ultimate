/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgUtils {

	private IcfgUtils() {
		// do not instantiate utility class
	}

	public static <LOC extends IcfgLocation> Set<LOC> getPotentialCycleProgramPoints(final IIcfg<LOC> icfg) {
		return new IcfgLocationIterator<>(icfg).asStream().filter(a -> a.getOutgoingEdges().stream().anyMatch(b -> {
			final LoopEntryAnnotation loa = LoopEntryAnnotation.getAnnotation(b);
			return loa != null && loa.getLoopEntryType() == LoopEntryType.GOTO;
		})).collect(Collectors.toSet());
	}

	/**
	 * @return {@link List} that contains all {@link IcfgEdge}s that originate from an initial location.
	 */
	public static <LOC extends IcfgLocation> List<IcfgEdge> extractStartEdges(final IIcfg<LOC> icfg) {
		return icfg.getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream()).collect(Collectors.toList());
	}

	public static <T extends IIcfgTransition<?>> UnmodifiableTransFormula getTransformula(final T transition) {
		if (transition instanceof IInternalAction) {
			return ((IInternalAction) transition).getTransformula();
		} else if (transition instanceof ICallAction) {
			return ((ICallAction) transition).getLocalVarsAssignment();
		} else if (transition instanceof IReturnAction) {
			return ((IReturnAction) transition).getAssignmentOfReturn();
		} else {
			throw new UnsupportedOperationException(
					"Dont know how to extract transformula from transition " + transition);
		}
	}

	public static <LOC extends IcfgLocation> Set<LOC> getErrorLocations(final IIcfg<LOC> icfg) {
		final Map<String, Set<LOC>> proc2ErrorLocations = icfg.getProcedureErrorNodes();
		final Set<LOC> errorLocs = new HashSet<>();
		for (final Entry<String, Set<LOC>> entry : proc2ErrorLocations.entrySet()) {
			errorLocs.addAll(entry.getValue());
		}
		return errorLocs;
	}

	public static <LOC extends IcfgLocation> boolean isErrorLocation(final IIcfg<LOC> icfg, final IcfgLocation loc) {
		if (icfg == null) {
			throw new IllegalArgumentException();
		}
		if (loc == null) {
			return false;
		}

		final String proc = loc.getProcedure();
		final Map<String, Set<LOC>> errorNodes = icfg.getProcedureErrorNodes();
		if (errorNodes == null || errorNodes.isEmpty()) {
			return false;
		}
		final Set<LOC> procErrorNodes = errorNodes.get(proc);
		if (procErrorNodes == null || procErrorNodes.isEmpty()) {
			return false;
		}
		return procErrorNodes.contains(loc);
	}

	public static <LOC extends IcfgLocation> int getNumberOfLocations(final IIcfg<LOC> icfg) {
		int result = 0;
		for (final Entry<String, Map<DebugIdentifier, LOC>> entry : icfg.getProgramPoints().entrySet()) {
			result += entry.getValue().size();
		}
		return result;
	}

	public static Set<IProgramVar> collectAllProgramVars(final CfgSmtToolkit csToolkit) {
		final Set<IProgramVar> result = new HashSet<>();
		for (final IProgramNonOldVar nonold : csToolkit.getSymbolTable().getGlobals()) {
			result.add(nonold);
			final IProgramOldVar oldVar = nonold.getOldVar();
			result.add(oldVar);
		}
		for (final String proc : csToolkit.getProcedures()) {
			for (final ILocalProgramVar local : csToolkit.getSymbolTable().getLocals(proc)) {
				result.add(local);
			}
		}
		return result;
	}

	/**
	 * Compute a hashcode for the graph structure of an ICFG. The hashcode is is only based on the hashcode of locations
	 * and edges and ignores {@link IProgramVar}s and other objects that come along with an ICFG. The method can help
	 * while debugging in order to find nondeterminism in our implementation.
	 */
	public static <LOC extends IcfgLocation> int computeIcfgHashCode(final IIcfg<LOC> icfg) {
		final IcfgLocationIterator<LOC> locIt = new IcfgLocationIterator<>(icfg);
		int result = 0;
		while (locIt.hasNext()) {
			final LOC loc = locIt.next();
			result += loc.hashCode();
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				result += edge.hashCode();
			}
		}
		return result;
	}

	public static <LOC extends IcfgLocation> boolean hasUnreachableProgramPoints(final IIcfg<LOC> icfg) {
		for (final Entry<String, Map<DebugIdentifier, LOC>> entry : icfg.getProgramPoints().entrySet()) {
			for (final Entry<DebugIdentifier, LOC> innerEntry : entry.getValue().entrySet()) {
				final LOC loc = innerEntry.getValue();
				if (loc.getIncomingEdges().isEmpty() && !isEntry(loc, icfg) && !isExit(loc, icfg)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * @return true iff loc is entry node of some procedure
	 */
	public static <LOC extends IcfgLocation> boolean isEntry(final LOC loc, final IIcfg<LOC> icfg) {
		return icfg.getProcedureEntryNodes().get(loc.getProcedure()).equals(loc);
	}

	/**
	 * @return true iff loc is exit node of some procedure
	 */
	public static <LOC extends IcfgLocation> boolean isExit(final LOC loc, final IIcfg<LOC> icfg) {
		return icfg.getProcedureExitNodes().get(loc.getProcedure()).equals(loc);
	}
}
