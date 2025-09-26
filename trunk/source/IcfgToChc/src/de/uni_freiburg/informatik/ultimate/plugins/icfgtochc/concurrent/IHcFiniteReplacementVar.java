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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * An interface for variables that can only take finitely many distinct values.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 */
public interface IHcFiniteReplacementVar extends IHcReplacementVar {
	/**
	 * The set of all possible values this variable can take. All terms must have the sort returned by
	 * {@link #getSort()}. The terms must not have free variables, nor refer to uninterpreted function symbols.
	 *
	 * For any two terms <code>t1</code> and <code>t2</code> in the returned set, either
	 * <code>Objects.equals(t1, t2)</code> must return <code>true</code>, or the equation <code>(= t1 t2)</code> must be
	 * unsatisfiable.
	 */
	Set<Term> getAllValues();
}
