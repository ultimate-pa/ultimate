/*
 * Copyright (C) 2025 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2025 University of Freiburg
 *
 * This file is part of the ULTIMATE Proofs Library.
 *
 * The ULTIMATE Proofs Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Proofs Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Proofs Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Proofs Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Proofs Library grant you additional permission
 * to convey the resulting work.
 */

/**
 * This package provides APIs for the generation, translation and validation of Floyd-Hoare annotations for graph-based
 * program representations such as control flow graphs
 * ({@link de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg}) or nested-word automata with
 * statement alphabets.
 *
 * A Floyd-Hoare annotation maps each node of such a graph to a logical formula over the program variables, and
 * satisfies certain additional properties (such as inductivity). When these properties are satisfied, a Floyd-Hoare
 * annotation serves as a proof that the program satisfies some (safety) specification. Floyd-Hoare annotations are the
 * primary proof artifact in Ultimate (at least, for sequential programs) and can be produced by various plugins, such
 * as TraceAbstraction, CodeCheck, or InvariantSynthesis.
 *
 * The interface representing Floyd-Hoare annotations in this package is
 * {@link de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare.IFloydHoareAnnotation}.
 */
package de.uni_freiburg.informatik.ultimate.lib.proofs.floydhoare;
