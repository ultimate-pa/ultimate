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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.ModifiableGlobalsTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormulaBuilder;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * A very simple implementation of a {@link ITransformulaTransformer}.
 *
 * Demonstrates the basic interface that should be used for loop acceleration transformers.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class CopyingTransformulaTransformer implements ITransformulaTransformer {

	private final ILogger mLogger;
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mOldSymbolTable;
	private final ModifiableGlobalsTable mOldModifiableGlobalsTable;

	/**
	 * Create an {@link CopyingTransformulaTransformer} instance.
	 *
	 * @param logger
	 *            A {@link ILogger} instance that is used for debug logging.
	 * @param loopBody
	 *            A {@link TransFormula} representing a loop body.
	 * @param managedScript
	 *            A {@link ManagedScript} instance that can be used to perform SMT operations.
	 * @param oldToolkit
	 *            The {@link CfgSmtToolkit} instance of the {@link IIcfg} for which this transformer is used.
	 */
	public CopyingTransformulaTransformer(final ILogger logger, final ManagedScript managedScript,
			final CfgSmtToolkit oldToolkit) {
		mLogger = logger;
		mManagedScript = Objects.requireNonNull(managedScript);
		mOldSymbolTable = oldToolkit.getSymbolTable();
		mOldModifiableGlobalsTable = oldToolkit.getModifiableGlobalsTable();
	}

	@Override
	public String getName() {
		return getClass().getSimpleName();
	}

	@Override
	public TransformulaTransformationResult transform(final IIcfgTransition<? extends IcfgLocation> oldEdge,
			final UnmodifiableTransFormula tf) {
		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Creating copy for " + tf);
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
		return mOldModifiableGlobalsTable.getProcToGlobals();
	}

}
