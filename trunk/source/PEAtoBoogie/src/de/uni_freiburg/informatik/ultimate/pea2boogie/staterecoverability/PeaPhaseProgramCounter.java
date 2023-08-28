/*
 * Copyright (C) 2023 Tobias Wießner <tobias.wiessner@mailbox.org>
 * Copyright (C) 2023 University of Freiburg
 *
 * This file is part of the ULTIMATE PEAtoBoogie plug-in.
 *
 * The ULTIMATE PEAtoBoogie plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE PEAtoBoogie plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE PEAtoBoogie plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE PEAtoBoogie plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE PEAtoBoogie plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.pea2boogie.staterecoverability;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.pea.Phase;
import de.uni_freiburg.informatik.ultimate.lib.pea.PhaseEventAutomata;
import de.uni_freiburg.informatik.ultimate.lib.srparse.pattern.PatternType;

/**
*
* @author Tobias Wießner <tobias.wiessner@mailbox.org>
*
*/

public class PeaPhaseProgramCounter {

	private final int pc;
	private final Phase phase;
	private final PhaseEventAutomata pea;
	private final PatternType<?> req;
	
	public PeaPhaseProgramCounter(final int pc, final Phase phase, final PhaseEventAutomata pea, final PatternType<?> req) {
		super();
		this.pc = pc;
		this.phase = phase;
		this.pea = pea;
		this.req = req;
	}

	@Override
	public int hashCode() {
		return phase.getName().hashCode();
	}
	
	@Override
	public boolean equals(Object o) {
		if(this == o) {
			return true;
		}
		if(o instanceof Phase) {
			Phase oPhase = (Phase) o;
			return phase.getName().equals(oPhase.getName());
		}
		return false;
	}

	public int getPc() {
		return pc;
	}

	public Phase getPhase() {
		return phase;
	}

	public PhaseEventAutomata getPea() {
		return pea;
	}
	
	public PatternType<?> getReq() {
		return req;
	}
}
