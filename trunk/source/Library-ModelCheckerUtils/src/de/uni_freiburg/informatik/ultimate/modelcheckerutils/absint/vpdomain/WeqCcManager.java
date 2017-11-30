/*
 * Copyright (C) 2017 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.vpdomain;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.CongruenceClosure;
import de.uni_freiburg.informatik.ultimate.util.datastructures.RemoveCcElement;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.PartialOrderCache;

public class WeqCcManager<NODE extends IEqNodeIdentifier<NODE>> {

	private final CcManager<NODE> mCcManager;

	public WeqCcManager(final IPartialComparator<CongruenceClosure<NODE>> ccComparator) {
		mCcManager = new CcManager<>(ccComparator);
	}

	WeqCongruenceClosure<NODE> getWeqMeet(final CongruenceClosure<NODE> cc,
			final WeqCongruenceClosure<NODE> weqcc, final RemoveCcElement<NODE> remInfo) {

		final WeqCongruenceClosure<NODE> result;
		if (remInfo == null) {
			result = weqcc.meetRec(cc);
		} else {
			assert false : "do we need this case?";
			result = null;
		}
		if (result.isInconsistent()) {
			return result;
		}
		return result;
	}

	public WeqCongruenceClosure<NODE> getWeqMeet(final CongruenceClosure<NODE> cc,
			final WeqCongruenceClosure<NODE> weqcc) {
		return getWeqMeet(cc, weqcc, null);
	}

	public WeqCongruenceClosure<NODE> addNode(final NODE node, final WeqCongruenceClosure<NODE> origWeqCc) {
		final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
		unfrozen.addElement(node);
		unfrozen.freeze();
		return unfrozen;
	}

	private WeqCongruenceClosure<NODE> unfreeze(final WeqCongruenceClosure<NODE> origWeqCc) {
		assert origWeqCc.isFrozen();
		return new WeqCongruenceClosure<>(origWeqCc, false);
	}

	public Set<CongruenceClosure<NODE>> filterRedundantCcs(final Set<CongruenceClosure<NODE>> ccs) {
		return mCcManager.filterRedundantCcs(ccs);
	}

	public IPartialComparator<CongruenceClosure<NODE>> getCcComparator() {
		return mCcManager.getCcComparator();
	}

	public CongruenceClosure<NODE> getMeet(final CongruenceClosure<NODE> cc1, final CongruenceClosure<NODE> cc2,
			final RemoveCcElement<NODE> elementCurrentlyBeingRemoved) {
		return mCcManager.getMeet(cc1, cc2, elementCurrentlyBeingRemoved);
	}

	public Set<CongruenceClosure<NODE>> filterRedundantCcs(final Set<CongruenceClosure<NODE>> ccs,
			final PartialOrderCache<CongruenceClosure<NODE>> ccPoCache) {
		return mCcManager.filterRedundantCcs(ccs, ccPoCache);
	}


	public WeqCongruenceClosure<NODE> reportEquality(final NODE node1, final NODE node2,
			final WeqCongruenceClosure<NODE> origWeqCc) {
		final WeqCongruenceClosure<NODE> unfrozen = unfreeze(origWeqCc);
		unfrozen.reportEquality(node1, node2);
		unfrozen.freeze();
		return unfrozen;
	}

	public WeqCongruenceClosure<NODE> makeCopyForWeqMeet(final WeqCongruenceClosure<NODE> originalPa) {
		return new WeqCongruenceClosure<>(originalPa, true);
	}

	public WeqCongruenceClosure<NODE> makeCopy(final WeqCongruenceClosure<NODE> original) {
		if (original.isFrozen()) {
			// original is frozen --> a copy should not be necessary (use unfreeze if an unfrozen copy is needed)
			return original;
		}
		return new WeqCongruenceClosure<>(original, false);
	}
}
