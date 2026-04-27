/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
 *
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BoogiePreprocessor plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BoogiePreprocessor plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BoogiePreprocessor plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BoogiePreprocessor plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.idps;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.boogie.ast.Declaration;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Procedure;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.SFO;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterruptServiceRoutinesBuilder {
	private final ISRInfo mIsrInfo;
	private final List<Declaration> mDeclarations;

	private final InterruptServiceRoutines mInterruptServiceRoutines;

	public InterruptServiceRoutinesBuilder(final List<Declaration> declarations, final ISRInfo isrInfo) {
		mDeclarations = declarations;
		mIsrInfo = isrInfo;
		mInterruptServiceRoutines = constructInterruptServiceRoutines();
	}

	private InterruptServiceRoutines constructInterruptServiceRoutines() {
		Procedure mainProcedure = null;
		final Map<Integer, Procedure> numToISR = new HashMap<>();
		final Map<Integer, Procedure> numToReqEnable = new HashMap<>();
		final Map<Integer, Procedure> numToReqDisable = new HashMap<>();
		final var isrNames = mIsrInfo.getISRMap().values();
		final var reqEnableNames = mIsrInfo.getRequestEnable().values();
		final var reqDisableNames = mIsrInfo.getRequestDisable().values();
		for (final Declaration declaration : mDeclarations) {
			if (!(declaration instanceof Procedure)) {
				continue;
			}
			final var proc = (Procedure) declaration;
			final var procId = proc.getIdentifier();
			if (isrNames.contains(procId)) {
				addProcToMap(numToISR, mIsrInfo.getISRMap(), proc);
			}
			if (reqEnableNames.contains(procId)) {
				addProcToMap(numToReqEnable, mIsrInfo.getRequestEnable(), proc);
			}

			if (reqDisableNames.contains(procId)) {
				addProcToMap(numToReqDisable, mIsrInfo.getRequestDisable(), proc);
			}

			if (procId.equals(SFO.MAIN)) {
				mainProcedure = proc;
			}

			// TODO: Implement for request disable and priority functions
		}
		return new InterruptServiceRoutines(numToISR, numToReqEnable, numToReqDisable, null, null, mainProcedure);
	}

	private void addProcToMap(final Map<Integer, Procedure> intProcMap, final Map<Integer, String> intIdMap,
			final Procedure proc) {
		final var procIdEntry = DataStructureUtils.getOneAndOnly(
				intIdMap.entrySet().stream().filter(e -> e.getValue().equals(proc.getIdentifier())).toList(),
				"Interrupt-Service-Routine");
		final var interruptNum = procIdEntry.getKey();
		final var lastVal = intProcMap.put(interruptNum, proc);
		assert lastVal == null : "ISR with name " + proc.getIdentifier() + " exists already in the Map!";
	}

	public InterruptServiceRoutines getInterruptServiceRoutines() {
		return mInterruptServiceRoutines;
	}
}
