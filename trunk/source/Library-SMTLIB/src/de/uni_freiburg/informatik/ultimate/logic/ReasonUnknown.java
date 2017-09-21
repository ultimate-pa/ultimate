/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

/**
 * The reason why we returned unknown. Note that the SMTLIB standard at the moment only allows "memout" and
 * "incomplete", but "timeout" and "crashed" and "cancelled" seem to be a good idea, too...
 * 
 * @author Juergen Christ
 */
public enum ReasonUnknown {
	MEMOUT {
		@Override
		public String toString() {
			return "memout";
		}
	},
	INCOMPLETE {
		@Override
		public String toString() {
			return "incomplete";
		}
	},
	TIMEOUT {
		@Override
		public String toString() {
			return "timeout";
		}
	},
	CRASHED {
		@Override
		public String toString() {
			return "crashed";
		}
	},
	CANCELLED {
		@Override
		public String toString() {
			return "cancelled";
		}
	},
	OTHER {
		@Override
		public String toString() {
			return "other";
		}
	}
}
