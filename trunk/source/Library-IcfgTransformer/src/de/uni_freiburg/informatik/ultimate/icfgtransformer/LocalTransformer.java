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

import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TermException;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.transformulatransformers.TransitionPreprocessor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * {@link ITransformulaTransformer} that can transform each {@link TransFormula}
 * separately (without knowing the whole ICFG and that uses 
 * {@link TransitionPreprocessor}s for this transformation.
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class LocalTransformer implements ITransformulaTransformer {
	
	private final TransitionPreprocessor mTransitionPreprocessor;
	private final ManagedScript mManagedScript;
	private final ReplacementVarFactory mReplacementVarFactory;
	
	public LocalTransformer(final TransitionPreprocessor transitionPreprocessor, final ManagedScript managedScript,
			final ReplacementVarFactory replacementVarFactory) {
		super();
		mTransitionPreprocessor = transitionPreprocessor;
		mManagedScript = managedScript;
		mReplacementVarFactory = replacementVarFactory;
	}

	@Override
	public UnmodifiableTransFormula transform(final UnmodifiableTransFormula tf) {
		final ModifiableTransFormula mod = ModifiableTransFormulaUtils.buildTransFormula(tf, mReplacementVarFactory, mManagedScript);
		try {
			final ModifiableTransFormula resultMod = mTransitionPreprocessor.process(mManagedScript.getScript(), mod);
			final UnmodifiableTransFormula result = TransFormulaBuilder.constructCopy(mManagedScript, resultMod, 
					Collections.emptySet(), Collections.emptySet(), Collections.emptyMap());
			return result;
		} catch (final TermException e) {
			throw new AssertionError(e);
		}
		
	}

	@Override
	public String getName() {
		return mTransitionPreprocessor.getDescription();
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mReplacementVarFactory.constructIIcfgSymbolTable();
	}

}
