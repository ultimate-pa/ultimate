/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.SimpleListable;

/**
 * A trigger that is activated when two values become equal. The two values are {@link CCParameter}s; the trigger fires
 * when their congruence classes are merged such that the values coincide (same representative and same offset to it).
 *
 * @author Tanja Schindler
 */
public abstract class CompareTrigger extends SimpleListable<CompareTrigger> {
	public abstract CCParameter getLhs();

	public abstract CCParameter getRhs();

	public abstract void activate();
}
