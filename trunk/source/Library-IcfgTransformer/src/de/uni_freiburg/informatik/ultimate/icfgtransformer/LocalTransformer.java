/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer;

import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TransitionPreprocessor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * {@link ITransformulaTransformer} that can transform each {@link TransFormula} separately (without knowing the whole
 * {@link IIcfg} and that uses {@link TransitionPreprocessor}s for this transformation.
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public final class LocalTransformer implements ITransformulaTransformer {

	private final List<TransitionPreprocessor> mTransitionPreprocessors;
	private final ManagedScript mManagedScript;
	private final ReplacementVarFactory mReplacementVarFactory;

	/**
	 * Default constructor.
	 *
	 * @param transitionPreprocessor
	 *            A single transition preprocessor that should be used.
	 * @param managedScript
	 *            A {@link ManagedScript} instance used to convert {@link UnmodifiableTransFormula}s to
	 *            {@link ModifiableTransFormula}s and back.
	 * @param replacementVarFactory
	 *            A {@link ReplacementVarFactory} instance.
	 */
	public LocalTransformer(final TransitionPreprocessor transitionPreprocessor, final ManagedScript managedScript,
			final ReplacementVarFactory replacementVarFactory) {
		this(Collections.singletonList(transitionPreprocessor), managedScript, replacementVarFactory);
	}

	/**
	 * Default constructor using a sequence of {@link TransitionPreprocessor}s.
	 *
	 * @param transitionPreprocessors
	 *            A {@link List} of {@link TransitionPreprocessor}s that should be used in that order.
	 * @param managedScript
	 *            A {@link ManagedScript} instance used to convert {@link UnmodifiableTransFormula}s to
	 *            {@link ModifiableTransFormula}s and back.
	 * @param replacementVarFactory
	 *            A {@link ReplacementVarFactory} instance.
	 */
	public LocalTransformer(final List<TransitionPreprocessor> transitionPreprocessors,
			final ManagedScript managedScript, final ReplacementVarFactory replacementVarFactory) {
		if (transitionPreprocessors == null || transitionPreprocessors.isEmpty()) {
			throw new IllegalArgumentException();
		}
		mTransitionPreprocessors = Collections.unmodifiableList(transitionPreprocessors);
		mManagedScript = Objects.requireNonNull(managedScript);
		mReplacementVarFactory = Objects.requireNonNull(replacementVarFactory);
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		final ModifiableTransFormula mod =
				ModifiableTransFormulaUtils.buildTransFormula(tf, mReplacementVarFactory, mManagedScript);
		try {
			ModifiableTransFormula resultMod = mod;
			for (final TransitionPreprocessor transformer : mTransitionPreprocessors) {
				final ModifiableTransFormula oldTf = resultMod;
				resultMod = transformer.process(mManagedScript, oldTf);
				assert transformer.checkSoundness(mManagedScript.getScript(), oldTf,
						resultMod) : "Transformation unsound for " + transformer.getDescription();
			}
			// local transformations are -- for now -- assumed to be always equivalent
			return new TransformulaTransformationResult(TransFormulaBuilder.constructCopy(mManagedScript, resultMod,
					Collections.emptySet(), Collections.emptySet(), Collections.emptyMap()));
		} catch (final TermException e) {
			throw new AssertionError(e);
		}

	}

	@Override
	public String getName() {
		if (mTransitionPreprocessors.size() == 1) {
			return mTransitionPreprocessors.iterator().next().getDescription();
		}
		return mTransitionPreprocessors.stream().map(TransitionPreprocessor::getDescription)
				.collect(Collectors.joining(","));
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mReplacementVarFactory.constructIIcfgSymbolTable();
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// A LocalTransformer needs no knowledge about the icfg.
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		// TODO: We construct ModifiableGlobalsTable here and in the usage. Seems strange, is there a reason?
		return mReplacementVarFactory.constructModifiableGlobalsTable().getProcToGlobals();
	}

}
