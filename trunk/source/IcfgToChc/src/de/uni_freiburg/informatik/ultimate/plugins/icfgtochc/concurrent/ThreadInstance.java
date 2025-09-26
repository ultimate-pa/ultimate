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
package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Comparator;
import java.util.Objects;

public final class ThreadInstance implements Comparable<ThreadInstance> {
	private final String mTemplateName;
	private final int mInstanceNumber;

	public ThreadInstance(final String templateName, final int instanceNumber) {
		mTemplateName = templateName;
		mInstanceNumber = instanceNumber;
	}

	public String getTemplateName() {
		return mTemplateName;
	}

	public int getInstanceNumber() {
		return mInstanceNumber;
	}

	@Override
	public int compareTo(final ThreadInstance o) {
		if (mInstanceNumber < 0 || o.mInstanceNumber < 0) {
			throw new UnsupportedOperationException("Must not compare interfering thread with this method.");
		}
		final var templateComparison = mTemplateName.compareTo(o.mTemplateName);
		if (templateComparison != 0) {
			return templateComparison;
		}
		return Integer.compare(mInstanceNumber, o.mInstanceNumber);
	}

	@Override
	public String toString() {
		return IcfgToChcConcurrentUtils.getReadableString(mTemplateName) + "_" + (mInstanceNumber + 1);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mInstanceNumber, mTemplateName);
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
		final ThreadInstance other = (ThreadInstance) obj;
		return mInstanceNumber == other.mInstanceNumber && Objects.equals(mTemplateName, other.mTemplateName);
	}

	public static Comparator<ThreadInstance> getNonInterferenceComparator(final int interferingIndex) {
		return (t1, t2) -> {
			if (t1.getInstanceNumber() >= 0 && t2.getInstanceNumber() >= 0) {
				// If not considering an interfering thread, use the usual ordering
				return t1.compareTo(t2);
			}

			// between threads of different templates, keep the same ordering as #compareTo
			// (i.e. order by template name)
			if (!t1.getTemplateName().equals(t2.getTemplateName())) {
				return t1.getTemplateName().compareTo(t2.getTemplateName());
			}
			if (t1.getInstanceNumber() >= 0) {
				// t2 is the interfering thread
				return t1.getInstanceNumber() < interferingIndex ? -1 : 1;
			}
			if (t2.getInstanceNumber() >= 0) {
				// t1 is the interfering thread
				return interferingIndex <= t2.getInstanceNumber() ? -1 : 1;
			}
			assert t1.equals(t2);
			return 0;
		};
	}
}
