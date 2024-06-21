/*
 * Copyright (C) 2024 Matthias Zumkeller
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.owickigries.empire;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class Federation<P> {
	Map<Set<P>, EmpireAnnotation<P>> mProofEmpireMap;
	EmpireAnnotation<P> mUnitedEmpire;

	public Federation(final Map<Set<P>, EmpireAnnotation<P>> proofEmpireMap) {
		mProofEmpireMap = proofEmpireMap;
		mUnitedEmpire = createUnitedEmpire();
	}

	private EmpireAnnotation<P> createUnitedEmpire() {
		final var empires = getEmpireAnnotations();
		final var unitedPairs = empires.stream().flatMap(e -> e.getEmpire().stream()).collect(Collectors.toSet());
		return new EmpireAnnotation<>(unitedPairs);
	}

	public Set<EmpireAnnotation<P>> getEmpireAnnotations() {
		return new HashSet<>(mProofEmpireMap.values());
	}

	public EmpireAnnotation<P> getProofsAnnotation(final Set<P> proofSet) {
		return mProofEmpireMap.get(proofSet);
	}

	public EmpireAnnotation<P> getUnitedEmpire() {
		return mUnitedEmpire;
	}

	@Override
	public String toString() {
		if (mProofEmpireMap.isEmpty()) {
			return "[empty empire]";
		}
		final var sb = new StringBuilder();
		for (final var entry : mProofEmpireMap.entrySet()) {
			final var empire = entry.getValue();
			sb.append("\t[\n");
			sb.append(empire);
			sb.append("\t]\n");
		}
		return sb.toString();
	}
}
