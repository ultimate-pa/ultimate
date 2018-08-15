/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration;

import java.util.Collections;
import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.icfgtransformer.ITransformulaTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * A very simple implementation of a {@link ITransformulaTransformer}.
 *
 * Demonstrates the basic interface that should be used for loop acceleration transformers.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class ExampleLoopAccelerationTransformulaTransformer implements ITransformulaTransformer {

	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mOldSymbolTable;

	/**
	 * Create an {@link ExampleLoopAccelerationTransformulaTransformer} instance.
	 *
	 * @param logger
	 *            A {@link ILogger} instance that is used for debug logging.
	 * @param loopBody
	 *            A {@link TransFormula} representing a loop body.
	 * @param managedScript
	 *            A {@link ManagedScript} instance that can be used to perform SMT operations.
	 * @param oldSymbolTable
	 *            An {@link IIcfgSymbolTable} instance that can be used to look up program variables of the loopBody
	 *            TransFormula.
	 * @param replacementVarFac
	 *            The {@link ReplacementVarFactory} instance which can create new (Term-)variables that represent
	 *            {@link Term}s of the old {@link TransFormula}.
	 */
	public ExampleLoopAccelerationTransformulaTransformer(final ILogger logger, final ManagedScript managedScript,
			final IIcfgSymbolTable oldSymbolTable, final ReplacementVarFactory replacementVarFac) {
		mLogger = logger;
		mManagedScript = Objects.requireNonNull(managedScript);
		mOldSymbolTable = oldSymbolTable;
	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Performing identity transformation for " + tf);
		}
		return new TransformulaTransformationResult(TransFormulaBuilder.constructCopy(mManagedScript, tf,
				Collections.emptySet(), Collections.emptySet(), Collections.emptyMap()));
	}

	@Override
	public IIcfgSymbolTable getNewIcfgSymbolTable() {
		return mOldSymbolTable;
	}

	@Override
	public void preprocessIcfg(final IIcfg<?> icfg) {
		// this transformer does not need any knowledge about the icfg
	}

	@Override
	public HashRelation<String, IProgramNonOldVar> getNewModifiedGlobals() {
		// TODO
		throw new UnsupportedOperationException("TODO");
	}

}
