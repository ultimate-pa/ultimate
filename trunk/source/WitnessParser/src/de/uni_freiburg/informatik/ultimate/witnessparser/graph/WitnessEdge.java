/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE WitnessParser plug-in.
 *
 * The ULTIMATE WitnessParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE WitnessParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE WitnessParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE WitnessParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE WitnessParser plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.witnessparser.graph;

import de.uni_freiburg.informatik.ultimate.core.lib.models.ModifiableMultigraphEdge;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

public class WitnessEdge extends ModifiableMultigraphEdge<WitnessNode, WitnessEdge, WitnessNode, WitnessEdge> {

	private static final long serialVersionUID = 1L;
	private final String mName;
	private final String mSourceCode;
	private final WitnessLocation mLocation;

	public WitnessEdge(final WitnessNode source, final WitnessNode target, final String id,
			final WitnessLocation location, final String sourcecode) {
		super(source, target);
		mName = id;
		mLocation = location;
		mSourceCode = sourcecode;
		redirectSource(source);
		redirectTarget(target);
	}

	public ILocation getLocation() {
		return mLocation;
	}

	public String getName() {
		return mName;
	}

	public String getSourceCode() {
		return mSourceCode;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		if (mName != null) {
			sb.append("[" + mName + "] ");
		}
		if (mLocation != null) {
			sb.append("L").append(mLocation.getStartLine()).append(" ");
		}
		if (mSourceCode != null) {
			sb.append(mSourceCode);
		}
		return sb.toString();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mLocation == null) ? 0 : mLocation.hashCode());
		result = prime * result + ((mName == null) ? 0 : mName.hashCode());
		result = prime * result + ((mSourceCode == null) ? 0 : mSourceCode.hashCode());
		return result;
	}

	@Override
	public WitnessEdge getLabel() {
		return this;
	}

}
