/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableExplicitEdgesMultigraph;
import de.uni_freiburg.informatik.ultimate.core.model.models.Payload;
import de.uni_freiburg.informatik.ultimate.core.model.models.annotation.Visualizable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.debugidentifiers.DebugIdentifier;

/**
 * Node of an interprocedureal control flow graph.
 *
 * @author heizmann@informatik.uni-freiburg.
 */
public class IcfgLocation extends ModifiableExplicitEdgesMultigraph<IcfgLocation, IcfgEdge, IcfgLocation, IcfgEdge>
		implements IIcfgElement {

	private static final long serialVersionUID = -7381268073266733825L;

	/**
	 * Procedure to which this location belongs to.
	 */
	@Visualizable
	private final String mProcedure;

	/**
	 * Unique identifier for debugging purposes.
	 */
	@Visualizable
	private final DebugIdentifier mDebugIdentifier;

	/**
	 *
	 * @param debugIdentifier
	 *            Note that this String must uniquely identify the node, inside its procedure, not only for debugging
	 *            purposes, but because it is used in hashCode() and equals().
	 * @param procedure
	 * @param payload
	 */
	public IcfgLocation(final DebugIdentifier debugIdentifier, final String procedure, final Payload payload) {
		super(payload);
		mProcedure = procedure;
		mDebugIdentifier = Objects.requireNonNull(debugIdentifier);
	}

	public IcfgLocation(final DebugIdentifier debugIdentifier, final String procedure) {
		this(debugIdentifier, procedure, null);
	}

	@Override
	public IcfgLocation getLabel() {
		return this;
	}

	public String getProcedure() {
		return mProcedure;
	}

	public DebugIdentifier getDebugIdentifier() {
		return mDebugIdentifier;
	}

	@Override
	public String toString() {
		return mDebugIdentifier.toString();
	}

	@Override
	public int hashCode() {
		return 3 * mDebugIdentifier.hashCode() + 5 * mProcedure.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final IcfgLocation other = (IcfgLocation) obj;
		if (mDebugIdentifier == null) {
			if (other.mDebugIdentifier != null) {
				return false;
			}
		} else if (!mDebugIdentifier.equals(other.mDebugIdentifier)) {
			return false;
		}
		if (mProcedure == null) {
			if (other.mProcedure != null) {
				return false;
			}
		} else if (!mProcedure.equals(other.mProcedure)) {
			return false;
		}
		return true;
	}
}
