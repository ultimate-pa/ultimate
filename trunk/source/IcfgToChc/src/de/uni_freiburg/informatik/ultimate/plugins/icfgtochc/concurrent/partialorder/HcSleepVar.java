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

import java.util.Objects;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IHcFiniteReplacementVar;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IHcThreadSpecificVar;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.ThreadInstance;

public class HcSleepVar implements IHcThreadSpecificVar, IHcFiniteReplacementVar {
	private final Sort mSort;
	private final ThreadInstance mInstance;
	private final Set<Term> mValues;

	public HcSleepVar(final ThreadInstance instance, final Script script) {
		this(instance, SmtSortUtils.getBoolSort(script),
				Set.of(script.term(SMTLIBConstants.TRUE), script.term(SMTLIBConstants.FALSE)));
	}

	private HcSleepVar(final ThreadInstance instance, final Sort sort, final Set<Term> values) {
		mInstance = instance;
		mSort = sort;
		mValues = values;
	}

	@Override
	public ThreadInstance getThreadInstance() {
		return mInstance;
	}

	@Override
	public IHcThreadSpecificVar forInstance(final int instanceId) {
		return new HcSleepVar(new ThreadInstance(mInstance.getTemplateName(), instanceId), mSort, mValues);
	}

	@Override
	public Set<Term> getAllValues() {
		return mValues;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public String toString() {
		return "sleep_" + mInstance;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		return prime * Objects.hash(mInstance);
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
		final HcSleepVar other = (HcSleepVar) obj;
		return Objects.equals(mInstance, other.mInstance);
	}
}
