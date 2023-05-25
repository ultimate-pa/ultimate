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

import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Represents an independence (or "commutativity" relation). In spirit, this interface is similar to
 * {@link IIndependenceRelation}, but instead of explicitly checking independence, it returns a symbolic condition (a
 * boolean {@link Term}) such that, if the term evaluates to {@code true}, then the given letters are independent.
 *
 * Symbolic independence relations are inherently conditional: The returned {@link Term} is a formula over program
 * variables that implies commutativity. However, symbolic independence relations currently do not support passing in a
 * known context.
 *
 * Similar to {@link IIndependenceRelation}s, symbolic independence relations can be symmetric (i.e., describe a
 * commutativity relation) or not (i.e., describe a semi-commutativity relation).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of actions checked for independence
 */
public interface ISymbolicIndependenceRelation<L> {
	Term getIndependenceCondition(L a, L b);

	boolean isSymmetric();
}