/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence;

/**
 * Bundles various settings specifying an independence relation to be used.
 *
 * @see de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class IndependenceSettings {

	/**
	 * Specifies the basic type of independence check.
	 */
	public enum IndependenceType {
		/**
		 * Use only syntactic criteria (e.g. accessed variables) to determine commutativity.
		 */
		SYNTACTIC,
		/**
		 * Use an SMT solver to determine commutativity based on action semantics.
		 */
		SEMANTIC,
	}

	/**
	 * Specifies a kind of abstraction to be integrated in the independence check.
	 */
	public enum AbstractionType {
		/**
		 * Do not apply any abstraction.
		 */
		NONE,
		/**
		 * Apply an abstraction that eliminates variables not used in the current proof candidate.
		 *
		 * @see de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.VariableAbstraction
		 */
		VARIABLES_GLOBAL,
		/**
		 * Apply an abstraction that eliminates variables not used in Hoare triples for the abstracted statement in the
		 * current proof candidate.
		 *
		 * @see de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.independence.abstraction.SpecificVariableAbstraction
		 */
		VARIABLES_LOCAL
	}

	private final IndependenceType mIndependenceType;
	private final AbstractionType mAbstractionType;
	private final boolean mUseConditional;
	private final boolean mUseSemiCommutativity;

	/**
	 * Creates default settings for a simple independence relation.
	 */
	public IndependenceSettings() {
		this(IndependenceType.SEMANTIC, AbstractionType.NONE, true, true);
	}

	public IndependenceSettings(final IndependenceType independenceType, final AbstractionType abstractionType,
			final boolean useConditional, final boolean useSemiCommutativity) {
		mIndependenceType = independenceType;
		mAbstractionType = abstractionType;
		mUseConditional = useConditional;
		mUseSemiCommutativity = useSemiCommutativity;
	}

	public IndependenceType getIndependenceType() {
		return mIndependenceType;
	}

	public AbstractionType getAbstractionType() {
		return mAbstractionType;
	}

	public boolean useConditional() {
		return mUseConditional;
	}

	public boolean useSemiCommutativity() {
		return mUseSemiCommutativity;
	}
}
