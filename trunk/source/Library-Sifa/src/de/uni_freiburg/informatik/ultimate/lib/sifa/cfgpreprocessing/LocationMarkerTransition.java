/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa.cfgpreprocessing;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.models.IPayload;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgInternalTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.sifa.regexdag.RegexDag;

/**
 * Transition to mark paths in {@link RegexDag}.
 * 
 * @author schaetzc@tf.uni-freiburg.de
 */
public class LocationMarkerTransition implements IIcfgInternalTransition<IcfgLocation> {

	private static final long serialVersionUID = 1L;
	private final IcfgLocation mMarkedTarget;

	public LocationMarkerTransition(final IcfgLocation markedTarget) {
		mMarkedTarget = markedTarget;
	}

	@Override
	public IcfgLocation getSource() {
		throw new UnsupportedOperationException();
	}

	@Override
	public IcfgLocation getTarget() {
		return mMarkedTarget;
	}

	@Override
	public IPayload getPayload() {
		return null;
	}

	@Override
	public boolean hasPayload() {
		return false;
	}

	@Override
	public String getPrecedingProcedure() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String getSucceedingProcedure() {
		throw new UnsupportedOperationException();
	}

	@Override
	public UnmodifiableTransFormula getTransformula() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return String.format("※ %s", mMarkedTarget);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mMarkedTarget);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj == null) {
			return false;
		} else if (getClass() != obj.getClass()) {
			return false;
		}
		final LocationMarkerTransition other = (LocationMarkerTransition) obj;
		return Objects.equals(mMarkedTarget, other.mMarkedTarget);
	}
}
