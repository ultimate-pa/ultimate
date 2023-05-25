/*
 * Copyright (C) 2023 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgToChc plug-in.
 *
 * The ULTIMATE IcfgToChc plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgToChc plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgToChc plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgToChc plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgToChc plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.partialorder;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ApproximateLockstepPreferenceOrder implements IThreadModularPreferenceOrder {
	private final Script mScript;
	private final Map<IcfgLocation, Integer> mDepth;

	protected ApproximateLockstepPreferenceOrder(final Script script, final Map<IcfgLocation, Integer> depth) {
		mScript = script;
		mDepth = depth;
	}

	@Override
	public Term getOrderConstraint(final IcfgLocation lesserLoc, final Term lesserLocTerm,
			final IcfgLocation greaterLoc, final Term greaterLocTerm, final Map<IcfgLocation, Integer> locationMap) {
		if (lesserLoc != null && greaterLoc != null) {
			return getOrderConstraint(lesserLoc, greaterLoc);
		}

		if (lesserLoc != null) {
			return getOrderConstraint(lesserLoc, greaterLocTerm, locationMap);
		}

		assert greaterLoc != null : "At least one location must be fixed";
		final var constraint = getOrderConstraint(greaterLoc, lesserLocTerm, locationMap);

		// invert the constraint, because we flipped greaterLoc and lesserLocTerm
		return SmtUtils.not(mScript, constraint);
	}

	private Term getOrderConstraint(final IcfgLocation lesserLoc, final IcfgLocation greaterLoc) {
		if (mDepth.get(lesserLoc) <= mDepth.get(greaterLoc)) {
			return mScript.term(SMTLIBConstants.TRUE);
		}
		return mScript.term(SMTLIBConstants.FALSE);
	}

	private Term getOrderConstraint(final IcfgLocation fixedLoc, final Term otherLoc,
			final Map<IcfgLocation, Integer> locationMap) {
		final var fixedDepth = mDepth.get(fixedLoc);

		final var greaterLocs = mDepth.entrySet().stream().filter(e -> e.getValue() >= fixedDepth)
				.map(e -> mDepth.get(e.getKey())).sorted().collect(Collectors.toList());
		final var locRanges = rangify(greaterLocs);

		final var disjuncts = new ArrayList<Term>();
		for (final var range : locRanges) {
			final var disjunct = getIntervalConstraint(otherLoc, range.getFirst(), range.getSecond());
			if (SmtUtils.isTrueLiteral(disjunct)) {
				return mScript.term(SMTLIBConstants.TRUE);
			}
			disjuncts.add(disjunct);
		}
		return SmtUtils.or(mScript, disjuncts);
	}

	// Partitions a sorted list of integers into a sequence of (inclusive) intervals.
	private static List<Pair<Integer, Integer>> rangify(final List<Integer> sortedValues) {
		final var result = new ArrayList<Pair<Integer, Integer>>();
		for (int idx = 0; idx < sortedValues.size();) {
			final int start = sortedValues.get(idx);
			int current = start;
			do {
				idx++;
				current++;
			} while (idx < sortedValues.size() && sortedValues.get(idx) == current);

			result.add(new Pair<>(start, current - 1));
		}

		return result;
	}

	private Term getIntervalConstraint(final Term element, final int lowerBound, final int upperBound) {
		assert lowerBound <= upperBound : "empty interval encountered";
		final Term upperTerm = SmtUtils.constructIntValue(mScript, BigInteger.valueOf(upperBound));

		if (lowerBound == upperBound) {
			return SmtUtils.binaryEquality(mScript, element, upperTerm);
		}

		final Term lowerTerm = SmtUtils.constructIntValue(mScript, BigInteger.valueOf(lowerBound));
		return SmtUtils.and(mScript, SmtUtils.leq(mScript, lowerTerm, element),
				SmtUtils.leq(mScript, element, upperTerm));
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	public static ApproximateLockstepPreferenceOrder create(final Script script, final IIcfg<?> icfg) {
		return new ApproximateLockstepPreferenceOrder(script, computeDepthMap(icfg));
	}

	protected static Map<IcfgLocation, Integer> computeDepthMap(final IIcfg<?> icfg) {
		final var result = new HashMap<IcfgLocation, Integer>();
		for (final var entry : icfg.getProcedureEntryNodes().values()) {
			computeDepthMap(result, entry);
		}
		return result;
	}

	private static void computeDepthMap(final Map<IcfgLocation, Integer> map, final IcfgLocation entry) {
		map.put(entry, 0);
		final var iterator = new IcfgEdgeIterator(entry.getOutgoingEdges());
		while (iterator.hasNext()) {
			final var edge = iterator.next();
			assert map.containsKey(edge.getSource()) : "depth of edge source node is unknown";
			final int sourceDepth = map.get(edge.getSource());
			map.merge(edge.getTarget(), sourceDepth + 1, Integer::min);
		}
	}
}
