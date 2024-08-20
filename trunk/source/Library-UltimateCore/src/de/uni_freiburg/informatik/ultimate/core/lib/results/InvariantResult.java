/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Core.
 *
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Core grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.lib.results;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.Check;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation;
import de.uni_freiburg.informatik.ultimate.core.lib.models.annotation.LoopEntryAnnotation.LoopEntryType;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.services.IBacktranslationService;

/**
 * Report an invariant that holds at ELEM which is a node in an Ultimate model.
 *
 * @author Matthias Heizmann
 */
public class InvariantResult<ELEM extends IElement> extends AbstractResultAtElement<ELEM> {
	private final String mInvariant;
	private final boolean mIsLoopLocation;
	private final Set<Check> mChecks;

	@SuppressWarnings("unchecked")
	public <E> InvariantResult(final String plugin, final ELEM element,
			final IBacktranslationService translatorSequence, final E invariant, final Set<Check> checks) {
		super(element, plugin, translatorSequence);
		// TODO: Another class instead of this boolean flag?
		final LoopEntryAnnotation loopAnnot = LoopEntryAnnotation.getAnnotation(element);
		mIsLoopLocation = loopAnnot != null && loopAnnot.getLoopEntryType() == LoopEntryType.WHILE;
		mInvariant = translatorSequence.translateExpressionWithContextToString(invariant, getLocation(),
				(Class<E>) invariant.getClass());
		mChecks = checks;
	}

	public String getInvariant() {
		return mInvariant;
	}

	@Override
	public String getShortDescription() {
		return mIsLoopLocation ? "Loop Invariant" : "Location Invariant";
	}

	@Override
	public String getLongDescription() {
		return (mIsLoopLocation ? "Derived loop invariant: " : "Derived location invariant: ") + mInvariant;
	}

	/**
	 * Represents the specifications to whose proof this invariant belongs.
	 */
	public Set<Check> getChecks() {
		return mChecks;
	}
}
