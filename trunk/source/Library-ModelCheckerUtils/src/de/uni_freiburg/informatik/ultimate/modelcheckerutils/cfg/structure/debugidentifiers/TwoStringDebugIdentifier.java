/*
 * Copyright (C) 2018 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2018 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.debugidentifiers;

/**
 * A {@link TwoStringDebugIdentifier} is a {@link DebugIdentifier} that consists of two strings. The first string is a
 * paremeter, the second one a forced constant.
 *
 * Note: Use only string constants as parameters, otherwise the memory consumption might be very large.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public abstract class TwoStringDebugIdentifier extends StringDebugIdentifier {

	public TwoStringDebugIdentifier(final String prefix) {
		super(prefix);
	}

	protected abstract String getSuffix();

	@Override
	public String toString() {
		return super.toString() + getSuffix();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((getSuffix() == null) ? 0 : getSuffix().hashCode());
		return result;
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
		final TwoStringDebugIdentifier other = (TwoStringDebugIdentifier) obj;
		if (getPrefix() == null) {
			if (other.getPrefix() != null) {
				return false;
			}
		} else if (!getPrefix().equals(other.getPrefix())) {
			return false;
		}
		if (getSuffix() == null) {
			if (other.getSuffix() != null) {
				return false;
			}
		} else if (!getSuffix().equals(other.getSuffix())) {
			return false;
		}
		return true;
	}

}
