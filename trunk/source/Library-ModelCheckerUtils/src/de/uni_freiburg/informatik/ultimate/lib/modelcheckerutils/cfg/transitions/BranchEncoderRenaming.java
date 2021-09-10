/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IActionWithBranchEncoders;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.Substitution;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * Represents a renaming of branch encoders, and provides several related utility functions.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class BranchEncoderRenaming {
	private final Map<TermVariable, TermVariable> mSubstitution;

	/**
	 * Create a new renaming.
	 *
	 * @param substitution
	 *            The substitution mapping underlying the instance.
	 */
	public BranchEncoderRenaming(final Map<TermVariable, TermVariable> substitution) {
		mSubstitution = Collections.unmodifiableMap(substitution);
	}

	public Map<TermVariable, TermVariable> getSubstitution() {
		return mSubstitution;
	}

	/**
	 * Applies the renaming to a given assignment of branch encoders.
	 *
	 * @param branchEncoders
	 *            The assignment to which the renaming shall be applied.
	 * @return An assignment mapping branch encoder x to the value of y in the input, if x is renamed to y.
	 */
	public Map<TermVariable, Boolean> applyToValues(final Map<TermVariable, Boolean> branchEncoders) {
		if (mSubstitution.isEmpty()) {
			return branchEncoders;
		}

		final Map<TermVariable, Boolean> result = new HashMap<>(branchEncoders);
		for (final var entry : mSubstitution.entrySet()) {
			final TermVariable original = entry.getKey();
			final TermVariable renamed = entry.getValue();
			final Boolean value = branchEncoders.get(renamed);

			assert value != null : "Branch indicator value unknown: " + renamed + " (renamed from " + original + ")";

			result.put(original, value);
			result.remove(renamed);
		}

		return Collections.unmodifiableMap(result);
	}

	/**
	 * Applies the renaming to a transformula with branch encoders, i.e., performs substitution.
	 *
	 * @param tf
	 *            The transformula in which branch encoders shall be renamed
	 * @param mgdScript
	 *            A managed script used to construct a new transformula
	 * @return A new transformula equal to the input, except that the branch encoders have been renamed
	 */
	public UnmodifiableTransFormula applyToTransFormula(final UnmodifiableTransFormula tf,
			final ManagedScript mgdScript) {
		assert mSubstitution.keySet().stream().allMatch(tf.getBranchEncoders()::contains);

		final TransFormulaBuilder tfb =
				new TransFormulaBuilder(tf.getInVars(), tf.getOutVars(), tf.getNonTheoryConsts().isEmpty(),
						tf.getNonTheoryConsts(), false, mSubstitution.values(), tf.getAuxVars().isEmpty());
		for (final TermVariable aux : tf.getAuxVars()) {
			tfb.addAuxVar(aux);
		}
		tfb.setInfeasibility(tf.isInfeasible());
		tfb.setFormula(new Substitution(mgdScript, mSubstitution).transform(tf.getFormula()));
		return tfb.finishConstruction(mgdScript);
	}

	/**
	 * Applies the renaming to an Icfg edge.
	 *
	 * @param edge
	 *            An Icfg edge in which branch encoders shall be renamed
	 * @param mgdScript
	 *            A managed script used in the construction of a new transformula
	 * @param edgeBuilder
	 *            Used to construct the renamed edge
	 * @return A new (internal) Icfg edge, where branch encoders have been renamed in the underlying transformula
	 */
	public IcfgEdge applyToIcfgEdge(final IcfgEdge edge, final ManagedScript mgdScript,
			final IcfgEdgeBuilder edgeBuilder) {
		if (!(edge instanceof IActionWithBranchEncoders)) {
			return edge;
		}
		final UnmodifiableTransFormula tf = ((IActionWithBranchEncoders) edge).getTransitionFormulaWithBranchEncoders();
		final UnmodifiableTransFormula renamedFirstTfWithBe = applyToTransFormula(tf, mgdScript);
		return edgeBuilder.constructInternalTransition(edge, edge.getSource(), edge.getTarget(), edge.getTransformula(),
				renamedFirstTfWithBe, false);
	}

	/**
	 * Creates a new renaming that replaces every branch encoder by a fresh copy.
	 *
	 * @param action
	 *            An action whose branch encoders form the domain of the renaming
	 * @param mgdScript
	 *            A managed script used to create fresh variables
	 * @return A new renaming instance
	 */
	public static BranchEncoderRenaming makeFresh(final IActionWithBranchEncoders action,
			final ManagedScript mgdScript) {
		final UnmodifiableTransFormula tf = action.getTransitionFormulaWithBranchEncoders();
		return new BranchEncoderRenaming(tf.getBranchEncoders().stream()
				.collect(Collectors.toUnmodifiableMap(Function.identity(), mgdScript::constructFreshCopy)));
	}

	/**
	 * Sequentially composes two renamings.
	 *
	 * Note: parameter order follows the convential for functional composition, which can be unintuitive.
	 *
	 * @param outer
	 *            The outer renaming (applied after the inner renaming)
	 * @param inner
	 *            The outer renaming (applied before the outer renaming)
	 * @return A new renaming combining the effect of the given inputs
	 */
	public static BranchEncoderRenaming compose(final BranchEncoderRenaming outer, final BranchEncoderRenaming inner) {
		if (outer == null) {
			return inner;
		}
		if (inner == null) {
			return outer;
		}

		final Map<TermVariable, TermVariable> result = new HashMap<>();
		final Set<TermVariable> intermediates = new HashSet<>();

		for (final var entry : inner.mSubstitution.entrySet()) {
			final TermVariable originalBE = entry.getKey();
			final TermVariable intermediateBE = entry.getValue();
			final TermVariable renamedBE = outer.mSubstitution.get(intermediateBE);
			if (renamedBE == null) {
				result.put(originalBE, intermediateBE);
			} else {
				result.put(originalBE, renamedBE);
				intermediates.add(intermediateBE);
			}
		}

		for (final var entry : outer.mSubstitution.entrySet()) {
			final TermVariable originalBE = entry.getKey();
			final TermVariable renamedBE = entry.getValue();
			if (!intermediates.contains(originalBE) && !result.containsKey(originalBE)) {
				result.put(originalBE, renamedBE);
			}
		}

		return new BranchEncoderRenaming(result);
	}

	@Override
	public String toString() {
		return mSubstitution.toString();
	}
}
